#![feature(test)]

use edit_tree::{Apply, EditTree, ToLowerCharVec};

extern crate test;

use test::{black_box, Bencher};

static FORM: &'static [&'static str] = &[
    "ist",
    "Gelegenheiten",
    "aufgegangen",
    "letzte",
    "storniert",
    "gratulierte",
    "gelenkt",
    "abgesessen",
];

static LEMMA: &'static [&'static str] = &[
    "sein",
    "Gelegenheit",
    "gehen",
    "letzt",
    "stornieren",
    "gratulieren",
    "lenken",
    "sitzen",
];

#[bench]
pub fn bench_get_graph(b: &mut Bencher) {
    for (form, lemma) in FORM
        .iter()
        .zip(LEMMA)
        .map(|(form, lemma)| (form.to_lower_char_vec(), lemma.to_lower_char_vec()))
    {
        b.iter(|| {
            black_box(edit_tree::get_graph(&form, &lemma));
        });
    }
}

#[bench]
pub fn bench_apply_graph(b: &mut Bencher) {
    let trees = FORM
        .iter()
        .zip(LEMMA)
        .map(|(form, lemma)| {
            edit_tree::get_graph(&form.to_lower_char_vec(), &lemma.to_lower_char_vec())
        })
        .collect::<Vec<EditTree<char>>>();
    for (form, tree) in FORM.iter().zip(&trees) {
        b.iter(|| {
            black_box(tree.apply(&form.to_lower_char_vec()));
        });
    }
}
