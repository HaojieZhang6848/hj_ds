//! 双向链表
//! 
//! `LinkedList`是一个双向链表，支持`append`、`prepend`、`insert_at`、`remove_at`、`pop`、`pop_front`等操作。此外，它还支持`Index`和`IndexMut`操作，可以通过下标访问或修改链表中的元素。
//! 
//! # Examples
//! 
//! ```
//! use hj_ds::linked_list::LinkedList;
//! 
//! let mut ll: LinkedList<i64> = LinkedList::new();
//! ll.append(1);
//! ll.append(2);
//! ll.append(3);
//! assert_eq!(format!("{}", ll), "[1,2,3]"); // [1,2,3]
//! 
//! ll.prepend(0);
//! assert_eq!(format!("{}", ll), "[0,1,2,3]"); // [0,1,2,3]
//! 
//! ll.pop_front();
//! assert_eq!(format!("{}", ll), "[1,2,3]"); // [1,2,3]
//! 
//! ll.pop();
//! assert_eq!(format!("{}", ll), "[1,2]"); // [1,2]
//! 
//! ll.insert_at(1, 114514);
//! assert_eq!(format!("{}", ll), "[1,114514,2]"); // [1,114514,2]
//! 
//! ll.remove_at(1);
//! assert_eq!(format!("{}", ll), "[1,2]"); // [1,2]
//! 
//! let val = ll[1];
//! assert_eq!(val, 2); // 2
//! 
//! ll[1] = 233333;
//! assert_eq!(format!("{}", ll), "[1,233333]"); // [1,233333]
//! ```
use std::{
    cell::RefCell,
    fmt::{self, Debug, Display},
    ops::{Index, IndexMut},
    rc::{Rc, Weak},
};

#[derive(Debug)]
struct LinkedListNode<T>
where
    T: Debug,
{
    data: Option<T>,
    next: Option<Rc<RefCell<LinkedListNode<T>>>>,
    prev: Option<Weak<RefCell<LinkedListNode<T>>>>,
}

impl<T> LinkedListNode<T>
where
    T: Debug,
{
    fn next(&self) -> Option<Rc<RefCell<LinkedListNode<T>>>> {
        self.next.clone()
    }
    fn prev(&self) -> Option<Weak<RefCell<LinkedListNode<T>>>> {
        self.prev.clone()
    }
}

/// 双向链表的迭代器
pub struct LinkedListIterator<'a, T>
where
    T: Debug,
{
    current: &'a LinkedListNode<T>,
    tail: Rc<RefCell<LinkedListNode<T>>>,
}

impl<'a, T> Iterator for LinkedListIterator<'a, T>
where
    T: Debug,
{
    type Item = &'a T;

    /// 返回下一个元素
    fn next(&mut self) -> Option<Self::Item> {
        let next = self.current.next();
        if let Some(next) = next {
            if Rc::ptr_eq(&next, &self.tail) {
                return None;
            }
            self.current = unsafe { &*next.as_ptr() };
            self.current.data.as_ref()
        } else {
            None
        }
    }
}

/// 双向链表
#[derive(Debug)]
pub struct LinkedList<T>
where
    T: Debug,
{
    head: Rc<RefCell<LinkedListNode<T>>>,
    tail: Rc<RefCell<LinkedListNode<T>>>,
    size: usize,
}

impl<T> Display for LinkedList<T>
where
    T: Display + Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;
        let iter = self.iter();
        let mut elems: Vec<String> = vec![];
        for e in iter {
            let s = format!("{:?}", e);
            elems.push(s);
        }
        write!(f, "{}", elems.join(","))?;
        write!(f, "]")
    }
}

impl<T> LinkedList<T>
where
    T: Debug,
{
    /// 创建一个新的双向链表，内容为空
    pub fn new() -> Self {
        let head = Rc::new(RefCell::new(LinkedListNode {
            data: None,
            next: None,
            prev: None,
        }));
        let tail = Rc::new(RefCell::new(LinkedListNode {
            data: None,
            next: None,
            prev: None,
        }));
        head.borrow_mut().next = Some(Rc::clone(&tail));
        tail.borrow_mut().prev = Some(Rc::downgrade(&head));

        LinkedList {
            head,
            tail,
            size: 0,
        }
    }

    /// 在链表尾部追加一个元素
    pub fn append(&mut self, data: T) {
        let new_node = Rc::new(RefCell::new(LinkedListNode {
            data: Some(data),
            next: None,
            prev: None,
        }));
        let sub_tail = self
            .tail
            .borrow()
            .prev()
            .expect("tail.prev is None, this should not happen")
            .upgrade()
            .expect("tail.prev is not a valid Weak reference, this should not happen");

        sub_tail.borrow_mut().next = Some(Rc::clone(&new_node));
        new_node.borrow_mut().next = Some(Rc::clone(&self.tail));
        self.tail.borrow_mut().prev = Some(Rc::downgrade(&new_node));
        new_node.borrow_mut().prev = Some(Rc::downgrade(&sub_tail));

        self.size += 1;
    }

    /// 在链表头部追加一个元素
    pub fn prepend(&mut self, data: T) {
        let new_node = Rc::new(RefCell::new(LinkedListNode {
            data: Some(data),
            next: None,
            prev: None,
        }));
        let sub_head = self
            .head
            .borrow()
            .next()
            .expect("head.next is None, this should not happen");

        self.head.borrow_mut().next = Some(Rc::clone(&new_node));
        new_node.borrow_mut().next = Some(Rc::clone(&sub_head));
        sub_head.borrow_mut().prev = Some(Rc::downgrade(&new_node));
        new_node.borrow_mut().prev = Some(Rc::downgrade(&self.head));

        self.size += 1;
    }

    /// 返回链表内元素的个数
    pub fn size(&self) -> usize {
        self.size
    }

    /// 在指定位置插入一个元素
    /// index是zero-based的，如果`index == size`，则相当于`append`；如果`index == 0`，则相当于`prepend`
    /// 如果`index > size`，则panic
    pub fn insert_at(&mut self, index: usize, data: T) {
        if index > self.size {
            panic!("index out of bounds");
        }

        if index == self.size {
            self.append(data);
            return;
        }

        if index == 0 {
            self.prepend(data);
            return;
        }

        let new_node = Rc::new(RefCell::new(LinkedListNode {
            data: Some(data),
            next: None,
            prev: None,
        }));
        let sub_node = self.node_at(index);
        let sub_prev = sub_node.borrow().prev().unwrap().upgrade().unwrap();

        sub_prev.borrow_mut().next = Some(Rc::clone(&new_node));
        new_node.borrow_mut().next = Some(Rc::clone(&sub_node));
        sub_node.borrow_mut().prev = Some(Rc::downgrade(&new_node));
        new_node.borrow_mut().prev = Some(Rc::downgrade(&sub_prev));

        self.size += 1;
    }

    /// 删除指定位置的元素
    /// index是zero-based的，如果`index == 0`，则相当于`pop_front`；如果`index == size - 1`，则相当于`pop`
    /// 如果`index >= size`，则panic
    pub fn remove_at(&mut self, index: usize) {
        if index >= self.size {
            panic!("index out of bounds");
        }

        if index == 0 {
            self.pop_front();
            return;
        }

        if index == self.size - 1 {
            self.pop();
            return;
        }

        let sub_node = self.node_at(index);
        let sub_prev = sub_node.borrow().prev().unwrap().upgrade().unwrap();
        let sub_next = sub_node.borrow().next().unwrap();

        sub_prev.borrow_mut().next = Some(Rc::clone(&sub_next));
        sub_next.borrow_mut().prev = Some(Rc::downgrade(&sub_prev));

        self.size -= 1;
    }

    /// 弹出链表尾部的元素
    pub fn pop(&mut self) -> Option<T> {
        if self.size == 0 {
            return None;
        }

        let sub_tail = self
            .tail
            .borrow()
            .prev()
            .expect("tail.prev is None, this should not happen")
            .upgrade()
            .expect("tail.prev is not a valid Weak reference, this should not happen");

        let sub_sub_tail = sub_tail
            .borrow()
            .prev()
            .expect("sub_tail.prev is None, this should not happen")
            .upgrade()
            .expect("sub_tail.prev is not a valid Weak reference, this should not happen");

        sub_sub_tail.borrow_mut().next = Some(Rc::clone(&self.tail));
        self.tail.borrow_mut().prev = Some(Rc::downgrade(&sub_sub_tail));

        // 尝试从Rc中拿回RefCell<T>的所有权（这里不应该失败）
        if let Ok(ref_cell) = Rc::try_unwrap(sub_tail) {
            let node = ref_cell.into_inner();
            self.size -= 1;
            return node.data;
        } else {
            panic!("sub_tail has multiple owners, this should not happen");
        }
    }

    /// 弹出链表头部的元素
    pub fn pop_front(&mut self) -> Option<T> {
        if self.size == 0 {
            return None;
        }

        let sub_head = self
            .head
            .borrow()
            .next()
            .expect("head.next is None, this should not happen");
        let sub_sub_head = sub_head
            .borrow()
            .next()
            .expect("sub_head.next is None, this should not happen");

        self.head.borrow_mut().next = Some(Rc::clone(&sub_sub_head));
        sub_sub_head.borrow_mut().prev = Some(Rc::downgrade(&self.head));

        // 尝试从Rc中拿回RefCell<T>的所有权（这里不应该失败）
        if let Ok(ref_cell) = Rc::try_unwrap(sub_head) {
            let node = ref_cell.into_inner();
            self.size -= 1;
            return node.data;
        } else {
            panic!("sub_head has multiple owners, this should not happen");
        }
    }

    fn node_at(&self, index: usize) -> Rc<RefCell<LinkedListNode<T>>> {
        if index >= self.size {
            panic!("index out of bounds");
        }

        if index < self.size / 2 {
            let mut ptr = self
                .head
                .borrow()
                .next()
                .expect("head.next is None, this should not happen");
            for _ in 0..index {
                let next = {
                    ptr.borrow()
                        .next()
                        .expect("ptr.next is None, this should not happen")
                };
                ptr = next;
            }
            ptr
        } else {
            let mut ptr = self
                .tail
                .borrow()
                .prev()
                .expect("tail.prev is None, this should not happen")
                .upgrade()
                .expect("tail.prev is not a valid Weak reference, this should not happen");
            for _ in 0..(self.size - index - 1) {
                let prev = {
                    ptr.borrow()
                        .prev()
                        .expect("ptr.prev is None, this should not happen")
                        .upgrade()
                        .expect("ptr.prev is not a valid Weak reference, this should not happen")
                };
                ptr = prev;
            }
            ptr
        }
    }

    /// 返回链表的迭代器
    pub fn iter(&self) -> LinkedListIterator<T> {
        LinkedListIterator {
            current: unsafe { &*self.head.as_ptr() },
            tail: Rc::clone(&self.tail),
        }
    }
}

impl<T> Index<usize> for LinkedList<T>
where
    T: Debug,
{
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        if index >= self.size {
            panic!("index out of bounds");
        }
        let node = self.node_at(index);
        let node = unsafe { &*node.as_ptr() };
        node.data.as_ref().unwrap()
    }
}

impl<T> IndexMut<usize> for LinkedList<T>
where
    T: Debug,
{
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index >= self.size {
            panic!("index out of bounds");
        }
        let node = self.node_at(index);
        let node = unsafe { &mut *node.as_ptr() };
        node.data.as_mut().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::prelude::*;
    use std::collections::HashSet;


    fn prepare_rand_nums(size: i32) -> Vec<i32> {
        let mut rng = thread_rng();
        let rand_nums = (0..size)
            .map(|_| rng.gen_range(i32::MIN..=i32::MAX))
            .collect::<HashSet<i32>>();
        rand_nums.into_iter().collect::<Vec<i32>>()
    }

    #[test]
    fn new() {
        let ll: LinkedList<i32> = LinkedList::new();
        assert_eq!(ll.size, 0);
        let ss = ll.to_string();
        assert_eq!(ss, "[]");
    }

    #[test]
    fn append() {
        let mut ll: LinkedList<i32> = LinkedList::new();
        let rand_nums = prepare_rand_nums(1000);
        let expected_str = format!("[{}]", rand_nums.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(","));
        
        for num in rand_nums.iter() {
            ll.append(*num);
        }

        assert_eq!(ll.size, 1000);

        let actual_str = ll.to_string();
        assert_eq!(actual_str, expected_str);
    }

    #[test]
    fn prepend() {
        let mut ll: LinkedList<i32> = LinkedList::new();
        let rand_nums = prepare_rand_nums(1000);
        let expected_str = format!("[{}]", rand_nums.iter().rev().map(|x| x.to_string()).collect::<Vec<String>>().join(","));
        
        for num in rand_nums.iter() {
            ll.prepend(*num);
        }

        assert_eq!(ll.size, 1000);

        let actual_str = ll.to_string();
        assert_eq!(actual_str, expected_str);
    }

    #[test]
    fn pop() {
        let mut ll: LinkedList<i32> = LinkedList::new();
        let mut rand_nums = prepare_rand_nums(1000);
        for num in rand_nums.iter() {
            ll.append(*num);
        }

        for _ in 0..1000 {
            let val = ll.pop();
            let val_expected = rand_nums.pop();
            assert_eq!(val, val_expected);
        }

        assert_eq!(ll.size, 0);
    }

    #[test]
    fn pop_front() {
        let mut ll: LinkedList<i32> = LinkedList::new();
        let mut rand_nums = prepare_rand_nums(1000);
        for num in rand_nums.iter() {
            ll.append(*num);
        }

        for _ in 0..1000 {
            let val = ll.pop_front();
            let val_expected = rand_nums.remove(0);
            assert_eq!(val, Some(val_expected));
        }

        assert_eq!(ll.size, 0);
    }

    #[test]
    fn index() {
        let mut ll: LinkedList<i32> = LinkedList::new();
        let rand_nums = prepare_rand_nums(1000);
        for num in rand_nums.iter() {
            ll.append(*num);
        }

        for i in 0..1000 {
            assert_eq!(ll[i], rand_nums[i as usize]);
        }
    }

    #[test]
    fn index_mut() {
        let mut ll: LinkedList<i32> = LinkedList::new();
        let rand_nums = prepare_rand_nums(1000);
        for num in rand_nums.iter() {
            ll.append(*num);
        }

        for i in 0..1000 {
            ll[i] = rand_nums[i as usize] + 1;
            assert_eq!(ll[i], rand_nums[i as usize] + 1);
        }
    }

    #[test]
    fn insert_at() {
        let mut ll = LinkedList::new();
        let mut rand_nums = prepare_rand_nums(1000);
        for num in rand_nums.iter() {
            ll.append(*num);
        }

        let index_to_insert = (0..10).map(|_| rand::thread_rng().gen_range(0..1000)).collect::<Vec<usize>>();
        let value_to_insert = (0..10).map(|_| rand::thread_rng().gen_range(i32::MIN..=i32::MAX)).collect::<Vec<i32>>();
        for i in 0..10 {
            let index = index_to_insert[i];
            let value = value_to_insert[i];
            rand_nums.insert(index, value);
            ll.insert_at(index, value);
        }

        let expected_str = format!("[{}]", rand_nums.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(","));
        let actual_str = ll.to_string();
        assert_eq!(actual_str, expected_str);
    }

    #[test]
    fn remove_at() {
        let mut ll = LinkedList::new();
        let mut rand_nums = prepare_rand_nums(1000);
        for num in rand_nums.iter() {
            ll.append(*num);
        }

        let index_to_remove = (0..10).map(|_| rand::thread_rng().gen_range(0..1000)).collect::<Vec<usize>>();
        for i in 0..10 {
            let index = index_to_remove[i];
            rand_nums.remove(index);
            ll.remove_at(index);
        }

        let expected_str = format!("[{}]", rand_nums.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(","));
        let actual_str = ll.to_string();
        assert_eq!(actual_str, expected_str);
    }

    #[test]
    fn iter() {
        let mut ll = LinkedList::new();
        let rand_nums = prepare_rand_nums(1000);
        for num in rand_nums.iter() {
            ll.append(*num);
        }

        let mut iter = ll.iter();
        for i in 0..1000 {
            assert_eq!(iter.next(), Some(&rand_nums[i as usize]));
        }
    }
}
