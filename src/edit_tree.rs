use std::cmp::Ordering;
use std::fmt::{Debug, Display, Error, Formatter};
use std::hash::Hash;

use seqalign::measures::LCSOp;
use seqalign::measures::LCS;
use seqalign::op::IndexedOperation;
use seqalign::Align;
use serde;
use serde::{Deserialize, Serialize};
use std::cmp::Eq;

lazy_static! {
    static ref MEASURE: LCS = { LCS::new(1, 1) };
}

/// Returns a graph representing an edit tree to derive `b` from `a`.
///
/// CAUTION when using with stringy types. UTF-8 multi byte chars will not be treated well. Consider
/// passing in &[char] instead.
pub fn get_graph<T: PartialEq + Eq + Clone + Debug>(a: &[T], b: &[T]) -> TreeNode<T> {
    *build_tree(a, b).unwrap()
}

/// Recursively builds an edit tree by applying itself to pre and suffix of the longest common substring.
///
fn build_tree<T: PartialEq + Eq + Clone + Debug>(
    form_ch: &[T],
    lem_ch: &[T],
) -> Option<Box<TreeNode<T>>> {
    if form_ch.is_empty() && lem_ch.is_empty() {
        return None;
    }

    let alignment = MEASURE.align(&form_ch, &lem_ch);
    let root = match longest_match(&alignment.edit_script()[..]) {
        Some(m) => TreeNode::MatchNode {
            pre: m.start_src,
            suf: (form_ch.len() - m.start_src) - m.length,
            left: build_tree(&form_ch[..m.start_src], &lem_ch[..m.start_targ]),
            right: build_tree(
                &form_ch[m.start_src + m.length..],
                &lem_ch[m.start_targ + m.length..],
            ),
        },
        None => TreeNode::ReplaceNode {
            replacee: form_ch.to_vec(),
            replacement: lem_ch.to_vec(),
        },
    };
    Some(Box::new(root))
}

/// Enum representing a `TreeNode` of an `Graph<TreeNode<T>,Place>`.
#[derive(Debug, PartialEq, Hash, Eq, Clone, Serialize, Deserialize)]
pub enum TreeNode<T: PartialEq + Eq + Clone + Debug> {
    MatchNode {
        pre: usize,
        suf: usize,
        left: Option<Box<TreeNode<T>>>,
        right: Option<Box<TreeNode<T>>>,
    },

    ReplaceNode {
        replacee: Vec<T>,
        replacement: Vec<T>,
    },
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

// Utility trait to convert strings to a vec containing lower cased chars
pub trait ToLowerCharVec {
    fn to_lower_char_vec(&self) -> Vec<char>;
}

impl<'a> ToLowerCharVec for &'a str {
    fn to_lower_char_vec(&self) -> Vec<char> {
        self.to_lowercase().chars().collect()
    }
}

/// Trait to apply an edit tree to a given form.
pub trait Apply<T: PartialEq> {
    fn apply(&self, form: &[T]) -> Option<Vec<T>>;
}

impl<T: PartialEq + Eq + Clone + Debug> Apply<T> for TreeNode<T> {
    /// Recursively applies the nodes stored in the edit tree. Returns `None` if the tree is not applicable to
    /// `form`.
    fn apply(&self, form: &[T]) -> Option<Vec<T>> {
        let form_len = form.len();
        match self {
            TreeNode::MatchNode {
                pre,
                suf,
                left,
                right,
            } => {
                if pre + suf >= form_len {
                    return None;
                }

                let res: Vec<T> = form[*pre..form_len - *suf].to_vec();

                let right = match right {
                    Some(right) => match right.apply(&form[form_len - *suf..]) {
                        Some(right) => right,
                        _ => return None,
                    },
                    None => vec![],
                };
                let mut left = match left {
                    Some(left) => match left.apply(&form[..*pre]) {
                        Some(left) => left,
                        _ => return None,
                    },
                    None => vec![],
                };

                left.extend(res);
                left.extend(right);
                Some(left)
            }

            TreeNode::ReplaceNode {
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

impl<'a, T: PartialEq + Eq + Clone + Debug> Display for TreeNode<T> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        match self {
            TreeNode::ReplaceNode {
                replacee,
                replacement,
            } => f.write_str(&format!("r('{:?}''{:?}')", replacee, replacement,)),
            TreeNode::MatchNode {
                pre,
                suf,
                left,
                right,
            } => f.write_str(&format!("({:?}p{}s{:?}{})", left, pre, right, suf)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{get_graph, Apply, ToLowerCharVec, TreeNode};
    use std::collections::HashSet;

    #[test]
    fn test_graph_equality_outcome() {
        let a = "hates".to_lower_char_vec();
        let b = "hate".to_lower_char_vec();
        let g = get_graph(a.as_slice(), b.as_slice());

        let a = "loves".to_lower_char_vec();
        let b = "love".to_lower_char_vec();
        let g1 = get_graph(a.as_slice(), b.as_slice());

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
        let g = get_graph(
            &"machen".to_lower_char_vec(),
            &"gemacht".to_lower_char_vec(),
        );
        let g1 = get_graph(
            &"lachen".to_lower_char_vec(),
            &"gelacht".to_lower_char_vec(),
        );

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
        let g = get_graph(&a, &b);

        let a = "lachen".to_lower_char_vec();
        let b = "gelacht".to_lower_char_vec();
        let g1 = get_graph(&a, &b);

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
        let mut set: HashSet<TreeNode<char>> = HashSet::default();
        let a = "abc".to_lower_char_vec();
        let b = "ab".to_lower_char_vec();
        let g1 = get_graph(&a, &b);

        let a = "aaa".to_lower_char_vec();
        let b = "aa".to_lower_char_vec();
        let g2 = get_graph(&a, &b);

        let a = "cba".to_lower_char_vec();
        let b = "ba".to_lower_char_vec();
        let g3 = get_graph(&a, &b);
        let g4 = get_graph(&a, &b);

        let a = "aaa".to_lower_char_vec();
        let b = "aac".to_lower_char_vec();
        let g5 = get_graph(&a, &b);

        let a = "dec".to_lower_char_vec();
        let b = "decc".to_lower_char_vec();
        let g6 = get_graph(&a, &a);
        let g7 = get_graph(&a, &b);

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
        let g = get_graph(a.as_slice(), b.as_slice());
        assert!(g.apply(&c).is_some());
    }
    #[test]
    fn test_graphs_inapplicable() {
        let g = get_graph(
            "abcdefg".to_lower_char_vec().as_slice(),
            "abc".to_lower_char_vec().as_slice(),
        );
        assert!(g.apply(&"abc".to_lower_char_vec().as_slice()).is_none());

        let g = get_graph(
            "abcdefg".to_lower_char_vec().as_slice(),
            "efg".to_lower_char_vec().as_slice(),
        );
        assert!(g.apply(&"efg".to_lower_char_vec().as_slice()).is_none());
    }
}
