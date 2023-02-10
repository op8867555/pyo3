//! Data types used to describe runtime Python types.

use std::borrow::Cow;
use std::fmt::{Display, Formatter};
use std::marker::PhantomData;

pub struct Typed<T>(PhantomData<T>);

impl<T> Typed<T> {
    pub fn new() -> Self {
        Self(PhantomData)
    }
}

pub trait WithTypeInfo {
    /// Extracts the type hint information for this type when it appears as a return value.
    ///
    /// For example, `Vec<u32>` would return `List[int]`.
    /// The default implementation returns `Any`, which is correct for any type.
    ///
    /// For most types, the return value for this method will be identical to that of [`WithTypeInfo::type_input`].
    /// It may be different for some types, such as `Dict`, to allow duck-typing: functions return `Dict` but take `Mapping` as argument.
    #[cfg(feature = "experimental-inspect")]
    fn type_output(&self) -> TypeInfo {
        self.type_input()
    }

    /// Extracts the type hint information for this type when it appears as an argument.
    ///
    /// For example, `Vec<u32>` would return `Sequence[int]`.
    /// The default implementation returns `Any`, which is correct for any type.
    ///
    /// For most types, the return value for this method will be identical to that of [`WithTypeInfo::type_output`].
    /// It may be different for some types, such as `Dict`, to allow duck-typing: functions return `Dict` but take `Mapping` as argument.
    #[cfg(feature = "experimental-inspect")]
    fn type_input(&self) -> TypeInfo {
        self.type_output()
    }
}

pub trait WithCustomTypeInfo{
    #[cfg(feature = "experimental-inspect")]
    fn type_output(&self) -> TypeInfo {
        self.type_input()
    }
    #[cfg(feature = "experimental-inspect")]
    fn type_input(&self) -> TypeInfo {
        self.type_output()
    }
}

/// Designation of a Python type.
///
/// This enum is used to handle advanced types, such as types with generics.
/// Its [`Display`] implementation can be used to convert to the type hint notation (e.g. `List[int]`).
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum TypeInfo {
    /// The type `typing.Any`, which represents any possible value (unknown type).
    Any,
    /// The type `typing.None`.
    None,
    /// The type `typing.NoReturn`, which represents functions that never return (they can still panic / throw, similar to `never` in Rust).
    NoReturn,
    /// The type `typing.Callable`.
    ///
    /// The first argument represents the parameters of the callable:
    /// - `Some` of a vector of types to represent the signature,
    /// - `None` if the signature is unknown (allows any number of arguments with type `Any`).
    ///
    /// The second argument represents the return type.
    Callable(Option<Vec<TypeInfo>>, Box<TypeInfo>),
    /// The type `typing.tuple`.
    ///
    /// The argument represents the contents of the tuple:
    /// - `Some` of a vector of types to represent the accepted types,
    /// - `Some` of an empty vector for the empty tuple,
    /// - `None` if the number and type of accepted values is unknown.
    ///
    /// If the number of accepted values is unknown, but their type is, use [`Self::UnsizedTypedTuple`].
    Tuple(Option<Vec<TypeInfo>>),
    /// The type `typing.Tuple`.
    ///
    /// Use this variant to represent a tuple of unknown size but of known types.
    ///
    /// If the type is unknown, or if the number of elements is known, use [`Self::Tuple`].
    UnsizedTypedTuple(Box<TypeInfo>),

    /// A union of multiple types.
    Union(Vec<TypeInfo>),

    /// An optional value.
    Optional(Box<TypeInfo>),

    Dict(Box<TypeInfo>, Box<TypeInfo>),

    Mapping(Box<TypeInfo>, Box<TypeInfo>),

    List(Box<TypeInfo>),

    Set(Box<TypeInfo>),

    FrozenSet(Box<TypeInfo>),

    Sequence(Box<TypeInfo>),

    Iterable(Box<TypeInfo>),

    Iterator(Box<TypeInfo>),

    Builtin(&'static str),

    /// A Python class.
    Class {
        /// The module this class comes from.
        module: ModuleName,
        /// The name of this class, as it appears in a type hint.
        name: Cow<'static, str>,
        /// The generics accepted by this class (empty vector if this class is not generic).
        type_vars: Vec<TypeInfo>,
    },
}

/// Declares which module a type is a part of.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ModuleName {
    /// The type is built-in: it doesn't need to be imported.
    Builtin,
    /// The type is in the current module: it doesn't need to be imported in this module, but needs to be imported in others.
    CurrentModule,
    /// The type is in the specified module.
    Module(Cow<'static, str>),
}

impl TypeInfo {
    /// Returns the module in which a type is declared.
    ///
    /// Returns `None` if the type is declared in the current module.
    pub fn module_name(&self) -> Option<&str> {
        match self {
            TypeInfo::Any
            | TypeInfo::None
            | TypeInfo::NoReturn
            | TypeInfo::Callable(_, _)
            | TypeInfo::Tuple(_)
            | TypeInfo::UnsizedTypedTuple(_)
            | TypeInfo::Union(_)
            | TypeInfo::Optional(_)
            | TypeInfo::Dict(_, _)
            | TypeInfo::Mapping(_, _)
            | TypeInfo::List(_)
            | TypeInfo::Set(_)
            | TypeInfo::FrozenSet(_)
            | TypeInfo::Sequence(_)
            | TypeInfo::Iterable(_)
            | TypeInfo::Iterator(_)
            | TypeInfo::Builtin(_) => Some("typing"),
            TypeInfo::Class { module, .. } => match module {
                ModuleName::Builtin => Some("builtins"),
                ModuleName::CurrentModule => None,
                ModuleName::Module(name) => Some(name),
            },
        }
    }

    /// Returns the name of a type.
    ///
    /// The name of a type is the part of the hint that is not generic (e.g. `List` instead of `List[int]`).
    pub fn name(&self) -> Cow<'_, str> {
        Cow::from(match self {
            TypeInfo::Any => "Any",
            TypeInfo::None => "None",
            TypeInfo::NoReturn => "NoReturn",
            TypeInfo::Callable(_, _) => "Callable",
            TypeInfo::Tuple(_) => "Tuple",
            TypeInfo::UnsizedTypedTuple(_) => "Tuple",
            TypeInfo::Class { name, .. } => name,
            TypeInfo::Union(_) => "Union",
            TypeInfo::Optional(_) => "Optional",
            TypeInfo::Dict(_, _) => "Dict",
            TypeInfo::Mapping(_, _) => "Mapping",
            TypeInfo::List(_) => "List",
            TypeInfo::Set(_) => "Set",
            TypeInfo::FrozenSet(_) => "FrozenSet",
            TypeInfo::Sequence(_) => "Sequence",
            TypeInfo::Iterable(_) => "Iterable",
            TypeInfo::Iterator(_) => "Iterator",
            TypeInfo::Builtin(_) => "Builtin",
        })
    }
}

// Utilities for easily instantiating TypeInfo structures for built-in/common types.
impl TypeInfo {
    /// The Python `Optional` type.
    pub fn optional_of(t: TypeInfo) -> TypeInfo {
        TypeInfo::Optional(Box::new(t))
    }

    /// The Python `Union` type.
    pub fn union_of(types: &[TypeInfo]) -> TypeInfo {
        TypeInfo::Union(types.to_vec())
    }

    /// The Python `List` type.
    pub fn list_of(t: TypeInfo) -> TypeInfo {
        TypeInfo::List(Box::new(t))
    }

    /// The Python `Sequence` type.
    pub fn sequence_of(t: TypeInfo) -> TypeInfo {
        TypeInfo::Sequence(Box::new(t))
    }

    /// The Python `Set` type.
    pub fn set_of(t: TypeInfo) -> TypeInfo {
        TypeInfo::Set(Box::new(t))
    }

    /// The Python `FrozenSet` type.
    pub fn frozen_set_of(t: TypeInfo) -> TypeInfo {
        TypeInfo::FrozenSet(Box::new(t))
    }

    /// The Python `Iterable` type.
    pub fn iterable_of(t: TypeInfo) -> TypeInfo {
        TypeInfo::Iterable(Box::new(t))
    }

    /// The Python `Iterator` type.
    pub fn iterator_of(t: TypeInfo) -> TypeInfo {
        TypeInfo::Iterator(Box::new(t))
    }

    /// The Python `Dict` type.
    pub fn dict_of(k: TypeInfo, v: TypeInfo) -> TypeInfo {
        TypeInfo::Dict(Box::new(k), Box::new(v))
    }

    /// The Python `Mapping` type.
    pub fn mapping_of(k: TypeInfo, v: TypeInfo) -> TypeInfo {
        TypeInfo::Mapping(Box::new(k), Box::new(v))
    }

    /// Convenience factory for non-generic builtins (e.g. `int`).
    pub fn builtin(name: &'static str) -> TypeInfo {
        TypeInfo::Builtin(name)
    }
}

impl Display for TypeInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeInfo::Any | TypeInfo::None | TypeInfo::NoReturn => write!(f, "{}", self.name()),
            TypeInfo::Callable(args, output) => {
                if let Some(args) = args {
                    write!(f, "Callable[[")?;
                    let mut is_first = true;
                    for arg in args {
                        if !is_first {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", arg)?;
                        is_first = false
                    }
                    write!(f, "], {}]", output)
                } else {
                    write!(f, "Callable[..., {}]", output)
                }
            }
            TypeInfo::Tuple(None) => write!(f, "Tuple[...]"),
            TypeInfo::Tuple(Some(args)) => {
                write!(f, "Tuple[")?;
                let mut is_first = true;
                for arg in args {
                    if !is_first {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                    is_first = false;
                }
                if args.is_empty() {
                    write!(f, "()")?;
                }
                write!(f, "]")
            }
            TypeInfo::UnsizedTypedTuple(arg) => write!(f, "Tuple[{arg}, ...]"),
            TypeInfo::Union(args) => {
                write!(f, "Union[")?;
                let mut is_first = true;
                for arg in args {
                    if !is_first {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                    is_first = false;
                }
                write!(f, "]")
            }
            TypeInfo::Optional(arg) => write!(f, "Optional[{arg}]"),
            TypeInfo::Dict(key, value) => write!(f, "Dict[{key}, {value}]"),
            TypeInfo::Mapping(key, value) => write!(f, "Mapping[{key}, {value}]"),
            TypeInfo::List(arg) => write!(f, "List[{arg}]"),
            TypeInfo::Set(arg) => write!(f, "Set[{arg}]"),
            TypeInfo::FrozenSet(arg) => write!(f, "FrozenSet[{arg}]"),
            TypeInfo::Sequence(arg) => write!(f, "Sequence[{arg}]"),
            TypeInfo::Iterator(arg) => write!(f, "Iterator[{arg}]"),
            TypeInfo::Iterable(arg) => write!(f, "Iterable[{arg}]"),
            TypeInfo::Builtin(name) => write!(f, "{}", name),
            TypeInfo::Class {
                name, type_vars, ..
            } => {
                write!(f, "{}", name)?;

                if !type_vars.is_empty() {
                    write!(f, "[")?;

                    let mut comma = false;
                    for var in type_vars {
                        if comma {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", var)?;
                        comma = true;
                    }

                    write!(f, "]")
                } else {
                    Ok(())
                }
            }
        }
    }
}

impl<T: crate::type_object::PyTypeInfo> WithTypeInfo for Typed<T> {
    fn type_input(&self) -> TypeInfo {
        TypeInfo::Class {
            name: ::std::borrow::Cow::Borrowed(T::NAME),
            module: T::MODULE
                .map(Cow::from)
                .map(ModuleName::Module)
                .unwrap_or(ModuleName::CurrentModule),
            type_vars: ::std::vec::Vec::new(),
        }
    }
}

impl<T> WithTypeInfo for &Typed<&T>
where
    Typed<T>: WithTypeInfo,
{
    fn type_input(&self) -> TypeInfo {
        (&&Typed::<T>::new()).type_input()
    }
    fn type_output(&self) -> TypeInfo {
        (&&Typed::<T>::new()).type_output()
    }
}

impl<T> WithTypeInfo for &&Typed<T>
where
    T: WithCustomTypeInfo,
{
    fn type_input(&self) -> TypeInfo {
        todo!()
    }
    fn type_output(&self) -> TypeInfo {
        todo!()
    }
}

impl WithTypeInfo for Typed<crate::class::basic::CompareOp> {
    fn type_input(&self) -> TypeInfo {
        TypeInfo::Any
    }
}

impl WithTypeInfo for Typed<()> {
    fn type_output(&self) -> TypeInfo {
        TypeInfo::None
    }
}

impl<T> WithTypeInfo for &Typed<crate::PyRef<'_, T>>
where
    T: crate::PyClass,
{
    fn type_input(&self) -> TypeInfo {
        TypeInfo::Class {
            name: ::std::borrow::Cow::Borrowed(T::NAME),
            module: T::MODULE
                .map(Cow::from)
                .map(ModuleName::Module)
                .unwrap_or(ModuleName::CurrentModule),
            type_vars: ::std::vec::Vec::new(),
        }
    }
}

impl<T> WithTypeInfo for &Typed<Option<T>>
where
    Typed<T>: WithTypeInfo,
{
    fn type_output(&self) -> TypeInfo {
        TypeInfo::Optional(Box::new((&&Typed::<T>::new()).type_output()))
    }

    fn type_input(&self) -> TypeInfo {
        TypeInfo::Optional(Box::new((&&Typed::<T>::new()).type_input()))
    }
}

impl<T, E> WithTypeInfo for &Typed<Result<T, E>>
where
    Typed<T>: WithTypeInfo,
{
    fn type_output(&self) -> TypeInfo {
        (&&Typed::<T>::new()).type_output()
    }

    fn type_input(&self) -> TypeInfo {
        (&&Typed::<T>::new()).type_input()
    }
}

impl<T> WithTypeInfo for &Typed<crate::Py<T>>
where
    Typed<T>: WithTypeInfo,
{
    fn type_output(&self) -> TypeInfo {
        (&&Typed::<T>::new()).type_output()
    }

    fn type_input(&self) -> TypeInfo {
        (&&Typed::<T>::new()).type_input()
    }
}

#[cfg(test)]
mod test {
    use std::borrow::Cow;

    use crate::inspect::types::{ModuleName, TypeInfo};

    pub fn assert_display(t: &TypeInfo, expected: &str) {
        assert_eq!(format!("{}", t), expected)
    }

    #[test]
    fn basic() {
        assert_display(&TypeInfo::Any, "Any");
        assert_display(&TypeInfo::None, "None");
        assert_display(&TypeInfo::NoReturn, "NoReturn");

        assert_display(&TypeInfo::builtin("int"), "int");
    }

    #[test]
    fn callable() {
        let any_to_int = TypeInfo::Callable(None, Box::new(TypeInfo::builtin("int")));
        assert_display(&any_to_int, "Callable[..., int]");

        let sum = TypeInfo::Callable(
            Some(vec![TypeInfo::builtin("int"), TypeInfo::builtin("int")]),
            Box::new(TypeInfo::builtin("int")),
        );
        assert_display(&sum, "Callable[[int, int], int]");
    }

    #[test]
    fn tuple() {
        let any = TypeInfo::Tuple(None);
        assert_display(&any, "Tuple[...]");

        let triple = TypeInfo::Tuple(Some(vec![
            TypeInfo::builtin("int"),
            TypeInfo::builtin("str"),
            TypeInfo::builtin("bool"),
        ]));
        assert_display(&triple, "Tuple[int, str, bool]");

        let empty = TypeInfo::Tuple(Some(vec![]));
        assert_display(&empty, "Tuple[()]");

        let typed = TypeInfo::UnsizedTypedTuple(Box::new(TypeInfo::builtin("bool")));
        assert_display(&typed, "Tuple[bool, ...]");
    }

    #[test]
    fn class() {
        let class1 = TypeInfo::Class {
            module: ModuleName::CurrentModule,
            name: Cow::from("MyClass"),
            type_vars: vec![],
        };
        assert_display(&class1, "MyClass");

        let class2 = TypeInfo::Class {
            module: ModuleName::CurrentModule,
            name: Cow::from("MyClass"),
            type_vars: vec![TypeInfo::builtin("int"), TypeInfo::builtin("bool")],
        };
        assert_display(&class2, "MyClass[int, bool]");
    }

    #[test]
    fn collections() {
        let int = TypeInfo::builtin("int");
        let bool = TypeInfo::builtin("bool");
        let str = TypeInfo::builtin("str");

        let list = TypeInfo::list_of(int.clone());
        assert_display(&list, "List[int]");

        let sequence = TypeInfo::sequence_of(bool.clone());
        assert_display(&sequence, "Sequence[bool]");

        let optional = TypeInfo::optional_of(str.clone());
        assert_display(&optional, "Optional[str]");

        let iterable = TypeInfo::iterable_of(int.clone());
        assert_display(&iterable, "Iterable[int]");

        let iterator = TypeInfo::iterator_of(bool);
        assert_display(&iterator, "Iterator[bool]");

        let dict = TypeInfo::dict_of(int.clone(), str.clone());
        assert_display(&dict, "Dict[int, str]");

        let mapping = TypeInfo::mapping_of(int, str.clone());
        assert_display(&mapping, "Mapping[int, str]");

        let set = TypeInfo::set_of(str.clone());
        assert_display(&set, "Set[str]");

        let frozen_set = TypeInfo::frozen_set_of(str);
        assert_display(&frozen_set, "FrozenSet[str]");
    }

    #[test]
    fn complicated() {
        let int = TypeInfo::builtin("int");
        assert_display(&int, "int");

        let bool = TypeInfo::builtin("bool");
        assert_display(&bool, "bool");

        let str = TypeInfo::builtin("str");
        assert_display(&str, "str");

        let any = TypeInfo::Any;
        assert_display(&any, "Any");

        let params = TypeInfo::union_of(&[int.clone(), str]);
        assert_display(&params, "Union[int, str]");

        let func = TypeInfo::Callable(Some(vec![params, any]), Box::new(bool));
        assert_display(&func, "Callable[[Union[int, str], Any], bool]");

        let dict = TypeInfo::mapping_of(int, func);
        assert_display(
            &dict,
            "Mapping[int, Callable[[Union[int, str], Any], bool]]",
        );
    }
}

#[cfg(test)]
mod conversion {
    use std::collections::{HashMap, HashSet};

    use crate::inspect::types::test::assert_display;
    use crate::inspect::types::WithTypeInfo;
    use crate::{FromPyObject, IntoPy};

    #[test]
    fn unsigned_int() {
        assert_display(&usize::type_output(), "int");
        assert_display(&usize::type_input(), "int");

        assert_display(&u8::type_output(), "int");
        assert_display(&u8::type_input(), "int");

        assert_display(&u16::type_output(), "int");
        assert_display(&u16::type_input(), "int");

        assert_display(&u32::type_output(), "int");
        assert_display(&u32::type_input(), "int");

        assert_display(&u64::type_output(), "int");
        assert_display(&u64::type_input(), "int");
    }

    #[test]
    fn signed_int() {
        assert_display(&isize::type_output(), "int");
        assert_display(&isize::type_input(), "int");

        assert_display(&i8::type_output(), "int");
        assert_display(&i8::type_input(), "int");

        assert_display(&i16::type_output(), "int");
        assert_display(&i16::type_input(), "int");

        assert_display(&i32::type_output(), "int");
        assert_display(&i32::type_input(), "int");

        assert_display(&i64::type_output(), "int");
        assert_display(&i64::type_input(), "int");
    }

    #[test]
    fn float() {
        assert_display(&f32::type_output(), "float");
        assert_display(&f32::type_input(), "float");

        assert_display(&f64::type_output(), "float");
        assert_display(&f64::type_input(), "float");
    }

    #[test]
    fn bool() {
        assert_display(&bool::type_output(), "bool");
        assert_display(&bool::type_input(), "bool");
    }

    #[test]
    fn text() {
        assert_display(&String::type_output(), "str");
        assert_display(&String::type_input(), "str");

        assert_display(&<&[u8]>::type_output(), "bytes");
        assert_display(&<&[u8]>::type_input(), "bytes");
    }

    #[test]
    fn collections() {
        assert_display(&<Vec<usize>>::type_output(), "List[int]");
        assert_display(&<Vec<usize>>::type_input(), "Sequence[int]");

        assert_display(&<HashSet<usize>>::type_output(), "Set[int]");
        assert_display(&<HashSet<usize>>::type_input(), "Set[int]");

        assert_display(&<HashMap<usize, f32>>::type_output(), "Dict[int, float]");
        assert_display(&<HashMap<usize, f32>>::type_input(), "Mapping[int, float]");

        assert_display(&<(usize, f32)>::type_input(), "Tuple[int, float]");
    }
}
