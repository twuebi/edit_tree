use std::cmp::Eq;
use std::cmp::Ordering;
use std::fmt;
use std::fmt::Debug;

use lazy_static::lazy_static;
use seqalign::measures::LCSOp;
use seqalign::measures::LCS;
use seqalign::op::IndexedOperation;
use seqalign::Align;
use serde::{Deserialize, Serialize};

lazy_static! {
    static ref MEASURE: LCS = { LCS::new(1, 1) };
}

/// Enum representing a `TreeNode` of an `Graph<TreeNode<T>,Place>`.
#[derive(Debug, PartialEq, Hash, Eq, Clone, Serialize, Deserialize)]
pub enum EditTree<T> {
    MatchNode {
        pre: usize,
        suf: usize,
        left: Option<Box<EditTree<T>>>,
        right: Option<Box<EditTree<T>>>,
    },

    ReplaceNode {
        replacee: Vec<T>,
        replacement: Vec<T>,
    },
}

impl<T> EditTree<T>
where
    T: PartialEq + Eq + Clone,
{
    /// Returns a edit tree specifying how to derive `b` from `a`.
    ///
    /// **Caution:** when using with stringy types. UTF-8 multi byte
    /// chars will not be treated well. Consider passing in &[char]
    /// instead.
    pub fn create_tree(a: &[T], b: &[T]) -> Option<Self> {
        build_tree(a, b).map(|tree| *tree)
    }

    /// Returns a s-String representation of the EditTree.
    ///
    /// `format_vec` defines how to transform the `Vec<T>` of a `ReplaceNode` into a
    /// `String`. This is useful when implementing `Display` for your own types where
    /// conversion to `String` may not be straight forward.
    pub fn pretty_print(&self, format_vec: impl (Fn(&[T]) -> String) + Copy) -> String {
        match self {
            EditTree::MatchNode {
                pre,
                suf,
                left,
                right,
            } => {
                let left_str = left
                    .as_ref()
                    .map(|left| left.pretty_print(format_vec))
                    .unwrap_or_else(|| "()".to_string());
                let right_str = right
                    .as_ref()
                    .map(|right| right.pretty_print(format_vec))
                    .unwrap_or_else(|| "()".to_string());

                format!("(match {} {} {} {})", pre, suf, left_str, right_str)
            }
            EditTree::ReplaceNode {
                replacee,
                replacement,
            } => format!(
                "(replace \"{}\" \"{}\")",
                format_vec(replacee),
                format_vec(replacement),
            ),
        }
    }
}

/// Struct representing a continuous match between two sequences.
#[derive(Debug, PartialEq, Eq, Hash, Ord)]
pub struct LCSMatch {
    start_src: usize,
    start_targ: usize,
    length: usize,
}

impl LCSMatch {
    pub fn new(start_src: usize, start_targ: usize, length: usize) -> Self {
        LCSMatch {
            start_src,
            start_targ,
            length,
        }
    }
    fn empty() -> Self {
        LCSMatch::new(0, 0, 0)
    }
}

impl PartialOrd for LCSMatch {
    fn partial_cmp(&self, other: &LCSMatch) -> Option<Ordering> {
        Some(self.length.cmp(&other.length))
    }
}

/// Returns the start and end index of the longest match. Returns none if no match is found.
fn longest_match(script: &[IndexedOperation<LCSOp>]) -> Option<LCSMatch> {
    let mut longest = LCSMatch::empty();

    let mut script_slice = &script[..];
    while !script_slice.is_empty() {
        let op = &script_slice[0];

        match op.operation() {
            LCSOp::Match => {
                let in_start = op.source_idx();
                let o_start = op.target_idx();
                let end = match script_slice.iter().position(|x| match x.operation() {
                    LCSOp::Match => false,
                    _ => true,
                }) {
                    Some(idx) => idx,
                    None => script_slice.len(),
                };
                if end > longest.length {
                    longest = LCSMatch::new(in_start, o_start, end);
                };

                script_slice = &script_slice[end..];
            }
            _ => {
                script_slice = &script_slice[1..];
            }
        }
    }

    if longest.length != 0 {
        Some(longest)
    } else {
        None
    }
}

/// Recursively builds an edit tree by applying itself to pre and suffix of the longest common substring.
fn build_tree<T: PartialEq + Eq + Clone>(form_ch: &[T], lem_ch: &[T]) -> Option<Box<EditTree<T>>> {
    if form_ch.is_empty() && lem_ch.is_empty() {
        return None;
    }

    let alignment = MEASURE.align(&form_ch, &lem_ch);
    let root = match longest_match(&alignment.edit_script()[..]) {
        Some(m) => EditTree::MatchNode {
            pre: m.start_src,
            suf: (form_ch.len() - m.start_src) - m.length,
            left: build_tree(&form_ch[..m.start_src], &lem_ch[..m.start_targ]),
            right: build_tree(
                &form_ch[m.start_src + m.length..],
                &lem_ch[m.start_targ + m.length..],
            ),
        },
        None => EditTree::ReplaceNode {
            replacee: form_ch.to_vec(),
            replacement: lem_ch.to_vec(),
        },
    };
    Some(Box::new(root))
}

/// Trait to apply an edit tree to a given form.
pub trait Apply<T: PartialEq> {
    fn apply(&self, form: &[T]) -> Option<Vec<T>>;
}

impl<T: PartialEq + Eq + Clone + Debug> Apply<T> for EditTree<T> {
    /// Recursively applies the nodes stored in the edit tree. Returns `None` if the tree is not applicable to
    /// `form`.
    fn apply(&self, form: &[T]) -> Option<Vec<T>> {
        let form_len = form.len();
        match self {
            EditTree::MatchNode {
                pre,
                suf,
                left,
                right,
            } => {
                if pre + suf >= form_len {
                    return None;
                }

                let mut left = match left {
                    Some(left) => left.apply(&form[..*pre])?,
                    None => vec![],
                };

                left.extend(form[*pre..form_len - *suf].iter().cloned());

                if let Some(right) = right {
                    left.extend(right.apply(&form[form_len - *suf..])?)
                }

                Some(left)
            }

            EditTree::ReplaceNode {
                ref replacee,
                ref replacement,
            } => {
                if form == &replacee[..] || replacee.is_empty() {
                    Some(replacement.clone())
                } else {
                    None
                }
            }
        }
    }
}

impl fmt::Display for EditTree<char> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            self.pretty_print(|chars: &[char]| chars.iter().collect::<String>())
        )
    }
}

#[cfg(test)]
mod tests {
    use super::{Apply, EditTree};
    use crate::ToLowerCharVec;
    use std::collections::HashSet;

    #[test]
    fn test_graph_equality_outcome() {
        let a = "hates".to_lower_char_vec();
        let b = "hate".to_lower_char_vec();
        let g = EditTree::create_tree(a.as_slice(), b.as_slice()).unwrap();

        let a = "loves".to_lower_char_vec();
        let b = "love".to_lower_char_vec();
        let g1 = EditTree::create_tree(a.as_slice(), b.as_slice()).unwrap();

        let f = "loves".to_lower_char_vec();
        let f1 = "hates".to_lower_char_vec();
        let exp = "love".to_lower_char_vec();
        let exp1 = "hate".to_lower_char_vec();

        assert_eq!(g.apply(&f1).unwrap(), exp1);
        assert_eq!(g1.apply(&f).unwrap(), exp);
        assert_eq!(g, g1);
    }

    #[test]
    fn test_graph_equality_outcome_2() {
        let g = EditTree::create_tree(
            &"machen".to_lower_char_vec(),
            &"gemacht".to_lower_char_vec(),
        )
        .unwrap();
        let g1 = EditTree::create_tree(
            &"lachen".to_lower_char_vec(),
            &"gelacht".to_lower_char_vec(),
        )
        .unwrap();

        let f = "machen".to_lower_char_vec();
        let f1 = "lachen".to_lower_char_vec();
        let exp = "gemacht".to_lower_char_vec();
        let exp1 = "gelacht".to_lower_char_vec();

        assert_eq!(g.apply(&f1).unwrap(), exp1);
        assert_eq!(g1.apply(&f).unwrap(), exp);
        assert_eq!(g, g1);
    }

    #[test]
    fn test_graph_equality_outcome_3() {
        let a = "aaaaaaaaen".to_lower_char_vec();
        let b = "geaaaaaaaat".to_lower_char_vec();
        let g = EditTree::create_tree(&a, &b).unwrap();

        let a = "lachen".to_lower_char_vec();
        let b = "gelacht".to_lower_char_vec();
        let g1 = EditTree::create_tree(&a, &b).unwrap();

        let f = "lachen".to_lower_char_vec();
        let f1 = "aaaaaaaaen".to_lower_char_vec();
        let exp = "gelacht".to_lower_char_vec();
        let exp1 = "geaaaaaaaat".to_lower_char_vec();

        assert_eq!(g.apply(&f).unwrap(), exp);
        assert_eq!(g1.apply(&f1).unwrap(), exp1);
        assert_eq!(g, g1);
    }

    #[test]
    fn test_graph_equality_and_applicability() {
        let mut set: HashSet<EditTree<char>> = HashSet::default();
        let a = "abc".to_lower_char_vec();
        let b = "ab".to_lower_char_vec();
        let g1 = EditTree::create_tree(&a, &b).unwrap();

        let a = "aaa".to_lower_char_vec();
        let b = "aa".to_lower_char_vec();
        let g2 = EditTree::create_tree(&a, &b).unwrap();

        let a = "cba".to_lower_char_vec();
        let b = "ba".to_lower_char_vec();
        let g3 = EditTree::create_tree(&a, &b).unwrap();
        let g4 = EditTree::create_tree(&a, &b).unwrap();

        let a = "aaa".to_lower_char_vec();
        let b = "aac".to_lower_char_vec();
        let g5 = EditTree::create_tree(&a, &b).unwrap();

        let a = "dec".to_lower_char_vec();
        let b = "decc".to_lower_char_vec();
        let g6 = EditTree::create_tree(&a, &a).unwrap();
        let g7 = EditTree::create_tree(&a, &b).unwrap();

        set.insert(g1);
        assert_eq!(set.len(), 1);
        set.insert(g2);
        assert_eq!(set.len(), 2);
        set.insert(g3);
        assert_eq!(set.len(), 3);
        set.insert(g4);
        assert_eq!(set.len(), 3);
        set.insert(g5);
        assert_eq!(set.len(), 4);
        set.insert(g6);
        set.insert(g7);
        assert_eq!(set.len(), 6);

        let v = "yyyy".to_lower_char_vec();
        let res: HashSet<String> = set
            .iter()
            .map(|x| x.apply(&v))
            .filter(|x| x.is_some())
            .map(|x| x.unwrap().iter().collect::<String>())
            .collect();

        assert_eq!(res.len(), 2);

        let v = "yyy".to_lower_char_vec();
        let res: HashSet<String> = set
            .iter()
            .map(|x| x.apply(&v))
            .filter(|x| x.is_some())
            .map(|x| x.unwrap().iter().collect::<String>())
            .collect();
        assert!(res.contains("yyyc"));
        assert!(res.contains("yyy"));
        assert_eq!(res.len(), 2);

        let v = "bba".to_lower_char_vec();
        let res: HashSet<String> = set
            .iter()
            .map(|x| x.apply(&v))
            .filter(|x| x.is_some())
            .map(|x| x.unwrap().iter().collect::<String>())
            .collect();

        assert!(res.contains("bbac"));
        assert!(res.contains("bba"));
        assert!(res.contains("bb"));
        assert!(res.contains("bbc"));
        assert_eq!(res.len(), 4);

        let v = a.as_slice();
        let res: HashSet<String> = set
            .iter()
            .map(|x| x.apply(&v))
            .filter(|x| x.is_some())
            .map(|x| x.unwrap().iter().collect::<String>())
            .collect();
        assert!(res.contains("dec"));
        assert!(res.contains("decc"));
        assert!(res.contains("de"));
        assert_eq!(res.len(), 3);

        let a = "die".to_lower_char_vec();
        let b = "das".to_lower_char_vec();
        let c = "die".to_lower_char_vec();
        let g = EditTree::create_tree(a.as_slice(), b.as_slice()).unwrap();
        assert!(g.apply(&c).is_some());
    }
    #[test]
    fn test_graphs_inapplicable() {
        let g = EditTree::create_tree(
            "abcdefg".to_lower_char_vec().as_slice(),
            "abc".to_lower_char_vec().as_slice(),
        )
        .unwrap();
        assert!(g.apply(&"abc".to_lower_char_vec().as_slice()).is_none());

        let g = EditTree::create_tree(
            "abcdefg".to_lower_char_vec().as_slice(),
            "efg".to_lower_char_vec().as_slice(),
        )
        .unwrap();
        assert!(g.apply(&"efg".to_lower_char_vec().as_slice()).is_none());
    }

    #[test]
    fn display_edit_tree() {
        let tree =
            EditTree::create_tree(&['l', 'o', 'o', 'p', 't'], &['l', 'o', 'p', 'e', 'n']).unwrap();

        assert_eq!(
            tree.to_string(),
            "(match 0 3 () (match 1 1 (replace \"o\" \"\") (replace \"t\" \"en\")))"
        );
    }
}
