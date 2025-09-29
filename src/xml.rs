// SPDX-FileCopyrightText: Copyright (c) 2022-2025 Objectionary.com
// SPDX-License-Identifier: MIT

use anyhow::Result;
use itertools::Itertools;
use xml_builder::{XMLBuilder, XMLElement, XMLVersion};

use crate::{Persistence, Sodg};

impl<const N: usize> Sodg<N> {
    /// Make XML graph.
    ///
    /// For example, for this code:
    ///
    /// ```
    /// use std::str::FromStr as _;
    /// use sodg::{Hex, Label};
    /// use sodg::Sodg;
    /// let mut g : Sodg<16> = Sodg::empty(256);
    /// g.add(0);
    /// g.put(0, &Hex::from_str_bytes("hello"));
    /// g.add(1);
    /// g.bind(0, 1, Label::from_str("foo").unwrap()).unwrap();
    /// g.bind(0, 1, Label::from_str("bar").unwrap()).unwrap();
    /// let xml = g.to_xml().unwrap();
    /// println!("{}", xml);
    /// ```
    ///
    /// The printout will look like this:
    ///
    /// ```xml
    /// <?xml version="1.1" encoding="UTF-8"?>
    /// <sodg>
    ///     <v id="0">
    ///         <e a="foo" to="1" />
    ///         <e a="bar" to="1" />
    ///         <data>68 65 6C 6C 6F</data>
    ///     </v>
    ///     <v id="1" />
    /// </sodg>
    /// ```
    ///
    /// # Errors
    ///
    /// If it's impossible to print it to XML, an [`Err`] may be returned. Problems may also
    /// be caused by XML errors from the XML builder library.
    pub fn to_xml(&self) -> Result<String> {
        let mut xml =
            XMLBuilder::new().version(XMLVersion::XML1_1).encoding("UTF-8".into()).build();
        let mut root = XMLElement::new("sodg");
        for (v, vtx) in self.vertices.iter().sorted_by_key(|(v, _)| <usize>::clone(v)) {
            let mut v_node = XMLElement::new("v");
            v_node.add_attribute("id", v.to_string().as_str());
            let mut edges = vtx
                .edges
                .iter()
                .map(|edge| (self.edge_label_text(edge).into_owned(), edge.to))
                .collect::<Vec<_>>();
            edges.sort_by(|left, right| left.0.cmp(&right.0));
            for (label, destination) in edges {
                let mut e_node = XMLElement::new("e");
                let to_attr = destination.to_string();
                e_node.add_attribute("a", label.as_str());
                e_node.add_attribute("to", to_attr.as_str());
                v_node.add_child(e_node)?;
            }
            if vtx.persistence != Persistence::Empty {
                let mut data_node = XMLElement::new("data");
                data_node.add_text(vtx.data.print().replace('-', " "))?;
                v_node.add_child(data_node)?;
            }
            root.add_child(v_node)?;
        }
        xml.set_root_element(root);
        let mut writer: Vec<u8> = Vec::new();
        xml.generate(&mut writer)?;
        Ok(std::str::from_utf8(&writer)?.to_string())
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr as _;

    use sxd_xpath::evaluate_xpath;

    use super::*;
    use crate::{Hex, Label};

    #[test]
    fn prints_simple_graph() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.add(0);
        g.put(0, &Hex::from_str_bytes("hello"));
        g.add(1);
        g.bind(0, 1, Label::from_str("foo").unwrap()).unwrap();
        let xml = g.to_xml().unwrap();
        let parser = sxd_document::parser::parse(xml.as_str()).unwrap();
        let doc = parser.as_document();
        assert_eq!("foo", evaluate_xpath(&doc, "/sodg/v[@id=0]/e[1]/@a").unwrap().string(),);
        assert_eq!(
            "68 65 6C 6C 6F",
            evaluate_xpath(&doc, "/sodg/v[@id=0]/data").unwrap().string(),
        );
    }
}
