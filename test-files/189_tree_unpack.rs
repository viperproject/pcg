enum Tree<T> {
    Nil,
    Node(T, Box<Tree<T>>, Box<Tree<T>>),
}

impl<T> Tree<T> {
    fn nil() -> Self {
        Tree::Nil
    }

    fn new(value: T, left: Self, right: Self) -> Self {
        Self::Node(value, Box::new(left), Box::new(right))
    }

    fn left(self) -> Self {
        match self {
            Self::Nil => Self::Nil,
            Self::Node(_, left, _) => *left,
        }
    }

    fn right(self) -> Self {
        match self {
            Self::Nil => Self::Nil,
            Self::Node(_, _, right) => *right,
        }
    }
}

enum LinkedList<T> {
    Empty,
    Node(T, Box<LinkedList<T>>),
}

impl<T> LinkedList<T> {
    fn new(head: T, tail: Option<Box<Self>>) -> Self {
        Self::Node(
            head,
            match tail {
                Some(tail) => tail,
                None => Box::new(Self::Empty),
            },
        )
    }
}

fn traverse<T>(tree: Tree<T>, path: LinkedList<bool>) -> Option<Tree<T>> {
    match path {
        LinkedList::Empty => Some(tree),
        LinkedList::Node(head, tail) => {
            if head {
                traverse(tree.left(), *tail)
            } else {
                traverse(tree.right(), *tail)
            }
        }
    }
}

fn dfs(tree: Box<Tree<i32>>, target: &i32) -> bool {
    match *tree {
        Tree::Nil => false,
        Tree::Node(value, left, right) => {
            if value == *target {
                return true;
            }
            if dfs(left, target) {
                true
            } else {
                dfs(right, target)
            }
        }
    }
}

fn main() {
    let left_child = Tree::new(10, Tree::Nil, Tree::Nil);
    let right_child = Tree::new(20, Tree::Nil, Tree::Nil);
    let tree = Tree::new(15, left_child, right_child);
    let target = 20;
}
