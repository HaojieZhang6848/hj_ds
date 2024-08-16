use hj_ds::linked_list::LinkedList;

fn main() {
    let mut ll: LinkedList<i64> = LinkedList::new();
    ll.append(1);
    ll.append(2);
    ll.append(3);

    println!("{}", ll); // [1,2,3]

    ll.prepend(0);
    println!("{}", ll); // [0,1,2,3]

    ll.pop_front();
    println!("{}", ll); // [1,2,3]

    ll.pop();
    println!("{}", ll); // [1,2]

    ll.insert_at(1, 114514);
    println!("{}", ll); // [1,114514,2]

    ll.remove_at(1);
    println!("{}", ll); // [1,2]

    let val = ll[1];
    println!("{}", val); // 2

    ll[1] = 233333;
    println!("{}", ll); // [1,233333]
}
