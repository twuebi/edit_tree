pub mod edit_tree;
pub use crate::edit_tree::{Apply, TreeNode};

// Utility trait to retrieve a lower-cased `Vec<char>`.
pub trait ToLowerCharVec {
    fn to_lower_char_vec(&self) -> Vec<char>;
}

impl<'a> ToLowerCharVec for &'a str {
    fn to_lower_char_vec(&self) -> Vec<char> {
        self.to_lowercase().chars().collect()
    }
}
