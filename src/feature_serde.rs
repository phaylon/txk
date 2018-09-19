
use std::fmt;
use std::marker;

use serde;

struct Visitor<K>(marker::PhantomData<K>);

impl<'de, K> serde::de::Visitor<'de> for Visitor<K>
where
    K: ::Kind,
{
    type Value = ::Text<K>;

    fn expecting(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "a valid {}", K::NAME)
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        ::Text::new(value).map_err(serde::de::Error::custom)
    }
}

impl<'de, K> serde::Deserialize<'de> for ::Text<K>
where
    K: ::Kind,
{
    fn deserialize<D>(deserializer: D) -> Result<::Text<K>, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_str(Visitor(marker::PhantomData))
    }
}

impl<K> serde::Serialize for ::Text<K>
where
    K: ::Kind,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.as_str())
    }
}
