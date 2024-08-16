//! 二叉搜索树
//! 
//! BST是一个二叉搜索树，支持插入、删除、查找、查找最接近的小于或小于等于给定值的元素、查找最接近的大于或大于等于给定值的元素等操作。
//! 
//! # Examples
//! 
//! ```
//! use hj_ds::bst::BST;
//! 
//! let mut bst: BST<i64> = BST::new();
//! 
//! bst.insert(3);
//! bst.insert(1);
//! bst.insert(8);
//! bst.insert(5);
//! bst.insert(10);
//! 
//! assert!(bst.contains(&3)); // true
//! assert!(bst.contains(&1)); // true
//! assert!(!bst.contains(&114514)); // false
//!
//! let ret = bst.remove(&3);
//! assert!(!bst.contains(&3)); // false
//! assert!(bst.contains(&1)); // true
//! assert_eq!(ret, Some(3));
//! 
//! let ret = bst.remove(&114514);
//! assert!(!bst.contains(&114514)); // false
//! assert_eq!(ret, None);
//!
//! assert_eq!(bst.ceil(&7), Some(&8)); // Some(&8)
//! assert_eq!(bst.ceil(&8), Some(&8)); // Some(&8)
//!
//! assert_eq!(bst.greater(&7), Some(&8)); // Some(&8)
//! assert_eq!(bst.greater(&8), Some(&10)); // Some(&10)
//!
//! assert_eq!(bst.floor(&7), Some(&5)); // Some(&5)
//! assert_eq!(bst.floor(&5), Some(&5)); // Some(&5)
//!
//! assert_eq!(bst.lower(&7), Some(&5)); // Some(&5)
//! assert_eq!(bst.lower(&5), Some(&1)); // Some(&1)
//! ```
struct BSTNode<T>
where
    T: Ord,
{
    data: T,
    left: Option<Box<BSTNode<T>>>,
    right: Option<Box<BSTNode<T>>>,
}

pub struct BST<T>
where
    T: Ord,
{
    root: Option<Box<BSTNode<T>>>,
    size: usize,
}

impl<T> BST<T>
where
    T: Ord,
{
    pub fn new() -> Self {
        BST {
            root: None,
            size: 0,
        }
    }

    /// 插入一个元素
    pub fn insert(&mut self, data: T) {
        let new_node = Box::new(BSTNode {
            data,
            left: None,
            right: None,
        });
        let data_ref = &new_node.data;
        if self.root.is_none() {
            self.root = Some(new_node);
            self.size += 1;
            return;
        }
        let mut ptr = self.root.as_mut().unwrap();
        loop {
            if data_ref < &ptr.data {
                if ptr.left.is_none() {
                    ptr.left = Some(new_node);
                    self.size += 1;
                    return;
                } else {
                    ptr = ptr.left.as_mut().unwrap();
                }
            } else if data_ref > &ptr.data {
                if ptr.right.is_none() {
                    ptr.right = Some(new_node);
                    self.size += 1;
                    return;
                } else {
                    ptr = ptr.right.as_mut().unwrap();
                }
            } else {
                return;
            }
        }
    }

    /// 查找一个元素
    pub fn contains(&self, data: &T) -> bool {
        let mut ptr = &self.root;
        while let Some(node) = ptr {
            let node_data = &node.data;
            if data < node_data {
                ptr = &node.left;
            } else if data > node_data {
                ptr = &node.right;
            } else {
                return true;
            }
        }
        false
    }

    /// 删除一个元素，返回被删除的元素
    pub fn remove(&mut self, data: &T) -> Option<T> {
        let removed;
        let val :Option<T>;
        (self.root, removed, val) = Self::remove_helper(self.root.take(), data);
        if removed {
            self.size -= 1;
        }
        val
    }

    fn remove_helper(root: Option<Box<BSTNode<T>>>, data: &T) -> (Option<Box<BSTNode<T>>>, bool, Option<T>) {
        let root = root;
        if root.is_none() {
            return (None, false, None);
        }
        let mut root = root.unwrap();
        let root_data = &root.data;
        if data < root_data {
            let left = root.left.take();
            let removed;
            let val;
            (root.left, removed, val) = Self::remove_helper(left, data);
            return (Some(root), removed, val);
        } else if data > root_data {
            let right = root.right.take();
            let removed;
            let val;
            (root.right, removed, val) = Self::remove_helper(right, data);
            return (Some(root), removed, val);
        } else {
            let right_is_none = root.right.is_none();
            let left_is_none = root.left.is_none();
            if right_is_none && left_is_none {
                return (None, true, Some(root.data));
            } else if right_is_none {
                return (root.left.take(), true, Some(root.data));
            } else if left_is_none {
                return (root.right.take(), true, Some(root.data));
            } else {
                let (node, min_val_in_right) = Self::get_and_remove_smallest(root.right);
                root.right = node;
                let ret_val = Some(root.data);
                root.data = min_val_in_right;
                return (Some(root), true, ret_val);
            }
        }
    }

    fn get_and_remove_smallest(root: Option<Box<BSTNode<T>>>) -> (Option<Box<BSTNode<T>>>, T) {
        let mut root = root.unwrap();
        if root.left.is_none() {
            return (root.right, root.data);
        }
        let (left, val) = Self::get_and_remove_smallest(root.left.take());
        root.left = left;
        (Some(root), val)
    }

    /// 查找最接近的严格小于给定值的元素
    pub fn lower(&self, data: &T) -> Option<&T> {
        Self::lower_helper(&self.root, data)
    }

    fn lower_helper<'a>(node: &'a Option<Box<BSTNode<T>>>, query: &T) -> Option<&'a T> {
        if node.is_none() {
            return None;
        }
        let node_data = &node.as_ref().unwrap().data;
        if node_data < query {
            let pos1 = Self::lower_helper(&node.as_ref().unwrap().right, query);
            if pos1.is_some() {
                return pos1;
            }
            return Some(node_data);
        } else {
            return Self::lower_helper(&node.as_ref().unwrap().left, query);
        }
    }

    /// 查找最接近的小于或等于给定值的元素
    pub fn floor(&self, data: &T) -> Option<&T> {
        let mut ptr = &self.root;
        while let Some(node) = ptr {
            let node_data = &node.data;
            if data < node_data {
                ptr = &node.left;
            } else if data > node_data {
                ptr = &node.right;
            } else {
                return Some(node_data);
            }
        }
        return self.lower(data);
    }

    /// 查找最接近的严格大于给定值的元素
    pub fn greater(&self, data: &T) -> Option<&T> {
        Self::greater_helper(&self.root, data)
    }

    fn greater_helper<'a>(node: &'a Option<Box<BSTNode<T>>>, query: &T) -> Option<&'a T> {
        if node.is_none() {
            return None;
        }
        let node_data = &node.as_ref().unwrap().data;
        if node_data > query {
            let pos1 = Self::greater_helper(&node.as_ref().unwrap().left, query);
            if pos1.is_some() {
                return pos1;
            }
            return Some(node_data);
        } else {
            return Self::greater_helper(&node.as_ref().unwrap().right, query);
        }
    }

    /// 查找最接近的大于或等于给定值的元素
    pub fn ceil(&self, data: &T) -> Option<&T> {
        let mut ptr = &self.root;
        while let Some(node) = ptr {
            let node_data = &node.data;
            if data < node_data {
                ptr = &node.left;
            } else if data > node_data {
                ptr = &node.right;
            } else {
                return Some(node_data);
            }
        }
        return self.greater(data);
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;
    use rand::prelude::*;

    fn prepare_rand_nums(size: i32) -> Vec<i32> {
        let mut rng = thread_rng();
        let rand_nums = (0..size)
            .map(|_| rng.gen_range(i32::MIN..=i32::MAX))
            .collect::<HashSet<i32>>();
        rand_nums.into_iter().collect::<Vec<i32>>()
    }

    #[test]
    fn bst_new() {
        let bst: BST<i32> = BST::new();
        assert!(bst.root.is_none())
    }

    #[test]
    fn insert_contains() {
        let mut bst = BST::new();
        let rand_nums = prepare_rand_nums(10000);
        let mid = rand_nums.len() / 2;
        let (list1, list2) = rand_nums.split_at(mid);

        for num in list1 {
            bst.insert(*num);
        }

        assert_eq!(bst.size, list1.len());

        for num in list1 {
            assert!(bst.contains(num));
        }

        for num in list2 {
            assert!(!bst.contains(num));
        }
    }

    #[test]
    fn remove_contains() {
        let mut bst = BST::new();
        let rand_nums = prepare_rand_nums(10000);
        let mid = rand_nums.len() / 2;
        let (list1, list2) = rand_nums.split_at(mid);

        for num in list1 {
            bst.insert(*num);
        }

        for num in list1 {
            assert!(bst.contains(num));
        }

        for i in 0..list1.len() {
            let num = list1[i];
            let ret = bst.remove(&num);
            assert_eq!(ret, Some(num));
            for j in i + 1..list1.len() {
                let num = list1[j];
                assert!(
                    bst.contains(&num),
                    "i: {}, j: {}, list1[i]: {}, list1[j]: {}",
                    i,
                    j,
                    list1[i],
                    list1[j]
                );
            }
            for j in 0..i {
                let num = list1[j];
                assert!(!bst.contains(&num));
            }
        }

        for num in list2 {
            assert!(!bst.contains(&num));
        }
    }

    #[test]
    pub fn remove2(){
        let strs = vec!["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"];
        let strs_clone = strs.clone();
        let mut bst = BST::new();
        for s in strs{
            bst.insert(s);
        }

        for s in strs_clone{
            let ret = bst.remove(&s);
            assert_eq!(ret, Some(s));
            assert_eq!(!bst.contains(&s), true);
        }

        assert!(bst.remove(&"t").is_none())
    }

    #[test]
    pub fn lower_floor() {
        let mut bst = BST::new();
        let mut rng = thread_rng();
        let mut rand_nums = prepare_rand_nums(10000);

        for num in &rand_nums {
            bst.insert(*num);
        }

        // 测试 lower和floor
        rand_nums.sort();
        // 在rand_nums[i]和rand_nums[i+1]之间随机生成一个数，然后查找这个数的lower和floor，看看是不是rand_nums[i]
        let mut i = 0;
        while i + 1 < rand_nums.len() {
            let a = rand_nums[i];
            let b = rand_nums[i + 1];
            if a + 1 < b {
                let lower_query = rng.gen_range(a + 1..b);
                let lower_rsp = bst.lower(&lower_query);
                assert!(lower_rsp.is_some());
                assert_eq!(lower_rsp.unwrap(), &a);

                let floor_query = rng.gen_range(a + 1..b);
                let floor_rsp = bst.floor(&floor_query);
                assert!(floor_rsp.is_some());
                assert_eq!(floor_rsp.unwrap(), &a);
            }
            i += 1;
        }

        // 测试rand_nums[0]的lower，应该是None
        let lower_rsp = bst.lower(rand_nums.first().unwrap());
        assert!(lower_rsp.is_none());

        // 测试rand_nums[len-1]+1的lower，应该是rand_nums[len-1]
        let last_val = rand_nums[rand_nums.len() - 1];
        if last_val < i32::MAX {
            let lower_rsp = bst.lower(&(last_val + 1));
            assert!(lower_rsp.is_some());
            assert_eq!(lower_rsp.unwrap(), &last_val);
        }

        // 在rand_nums中的所有元素上测试floor，看看是不是rand_nums[i]
        for i in 0..rand_nums.len() {
            let query = rand_nums[i];
            let rsp = bst.floor(&query);
            assert!(rsp.is_some());
            assert_eq!(rsp.unwrap(), &rand_nums[i]);
        }
    }

    #[test]
    pub fn grater_ceil() {
        let mut bst = BST::new();
        let mut rng = thread_rng();
        let mut rand_nums = prepare_rand_nums(10000);

        for num in &rand_nums {
            bst.insert(*num);
        }

        // 测试 greater和ceil
        rand_nums.sort();
        // 在rand_nums[i]和rand_nums[i+1]之间随机生成一个数，然后查找这个数的greater和ceil，看看是不是rand_nums[i+1]
        let mut i = 0;
        while i + 1 < rand_nums.len() {
            let a = rand_nums[i];
            let b = rand_nums[i + 1];
            if a + 1 < b {
                let greater_query = rng.gen_range(a + 1..b);
                let greater_rsp = bst.greater(&greater_query);
                assert!(greater_rsp.is_some());
                assert_eq!(greater_rsp.unwrap(), &b);

                let ceil_query = rng.gen_range(a + 1..b);
                let ceil_rsp = bst.ceil(&ceil_query);
                assert!(ceil_rsp.is_some());
                assert_eq!(ceil_rsp.unwrap(), &b);
            }
            i += 1;
        }

        // 测试rand_nums[0]-1的greater，应该是rand_nums[0]
        let query = rand_nums.first().unwrap() - 1;
        if query > i32::MIN {
            let grater_rsp = bst.greater(&query);
            assert!(grater_rsp.is_some());
            assert_eq!(grater_rsp.unwrap(), rand_nums.first().unwrap());
        }

        // 测试rand_nums[len-1]的greater，应该是None
        let last_val = rand_nums[rand_nums.len() - 1];
        let grater_rsp = bst.greater(&last_val);
        assert!(grater_rsp.is_none());

        // 在rand_nums中的所有元素上测试ceil，看看是不是rand_nums[i]
        for i in 0..rand_nums.len() {
            let query = rand_nums[i];
            let rsp = bst.floor(&query);
            assert!(rsp.is_some());
            assert_eq!(rsp.unwrap(), &rand_nums[i]);
        }
    }

    #[test]
    fn size(){
        // 测试有插入已存在的元素 或者 删除不存在的元素时，size是否还能正确计算
        let mut bst = BST::new();
        let mut rng = thread_rng();
        let (rand_nums, rand_nums_set)= loop {
            // 生成1000个0-2000的随机数，很大概率会有重复
            let rand_nums = (0..1000).map(|_| rng.gen_range(0..=2000)).collect::<Vec<i32>>(); 
            let rand_nums_set = rand_nums.iter().cloned().collect::<HashSet<i32>>();
            if rand_nums.len() > rand_nums_set.len(){
                break (rand_nums, rand_nums_set);
            }
        };
        for num in &rand_nums {
            bst.insert(*num);
        }
        assert_eq!(bst.size, rand_nums_set.len());
        for num in &rand_nums {
            bst.insert(*num);
        }
        assert_eq!(bst.size, rand_nums_set.len());

        for num in &rand_nums {
            bst.remove(num);
        }
        assert_eq!(bst.size, 0);
        for num in &rand_nums {
            bst.remove(num);
        }
        assert_eq!(bst.size, 0);
    }
}
