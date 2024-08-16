use hj_ds::bst::BST;

fn main() {
    let mut bst: BST<i64> = BST::new();
    bst.insert(3);
    bst.insert(1);
    bst.insert(8);
    bst.insert(5);
    bst.insert(10);

    println!("{}", bst.contains(&3)); // true
    println!("{}", bst.contains(&1)); // true
    println!("{}", bst.contains(&114514)); // false

    bst.remove(&3);
    println!("{}", bst.contains(&3)); // false
    println!("{}", bst.contains(&1)); // true

    println!("{:?}", bst.ceil(&7)); // Some(8)
    println!("{:?}", bst.ceil(&8)); // Some(8)

    println!("{:?}", bst.greater(&7)); // Some(8)
    println!("{:?}", bst.greater(&8)); // Some(10)

    println!("{:?}", bst.floor(&7)); // Some(5)
    println!("{:?}", bst.floor(&5)); // Some(5)

    println!("{:?}", bst.lower(&7)); // Some(5)
    println!("{:?}", bst.lower(&5)); // Some(1)
}
