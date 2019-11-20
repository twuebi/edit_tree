#[macro_use]
extern crate lazy_static;
extern crate failure;

pub mod edit_tree;
pub use crate::edit_tree::{Apply, ToLowerCharVec, TreeNode};
