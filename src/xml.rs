// SPDX-FileCopyrightText: Copyright (c) 2022-2026 Objectionary.com
// SPDX-License-Identifier: MIT

use anyhow::Result;
use itertools::Itertools as _;
use xml_builder::{XMLBuilder, XMLElement, XMLVersion};

use crate::{Kind, Sodg};

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
    /// g.formation(0, &[]);
    /// g.delta(0, &Hex::from_str_bytes("hello"));
    /// g.formation(1, &[]);
    /// g.put(0, Label::from_str("foo").unwrap(), 1);
    /// g.put(0, Label::from_str("bar").unwrap(), 1);
    /// let xml = g.to_xml().unwrap();
    /// println!("{}", xml);
    /// ```
    ///
    /// The printout will look like this:
    ///
    /// ```xml
    /// <?xml version="1.1" encoding="UTF-8"?>
    /// <sodg>
    ///     <cell id="0" kind="formation">
    ///         <e a="foo" to="1" />
    ///         <e a="bar" to="1" />
    ///         <data>68 65 6C 6C 6F</data>
    ///     </cell>
    ///     <cell id="1" kind="formation" />
    /// </sodg>
    /// ```
    ///
    /// # Errors
    ///
    /// If it's impossible to print it to XML, an [`Err`] may be returned. Problems may also
    /// be caused by XML errors from the XML builder library.
    pub fn to_xml(&self) -> Result<String> {
        let mut xml = XMLBuilder::new()
            .version(XMLVersion::XML1_1)
            .encoding("UTF-8".into())
            .build();
        let mut root = XMLElement::new("sodg");
        for (v, cell) in self
            .cells
            .iter()
            .filter(|(_, cell)| cell.made)
            .sorted_by_key(|(v, _)| *v)
        {
            let mut c_node = XMLElement::new("cell");
            c_node.add_attribute("id", v.to_string().as_str());
            match cell.kind {
                Kind::Void => {}
                Kind::Formation => c_node.add_attribute("kind", "formation"),
                Kind::Dispatch(a) => {
                    c_node.add_attribute("kind", "dispatch");
                    c_node.add_attribute("attr", a.to_string().as_str());
                }
                Kind::Application(a) => {
                    c_node.add_attribute("kind", "application");
                    c_node.add_attribute("attr", a.to_string().as_str());
                }
                Kind::Termination => c_node.add_attribute("kind", "termination"),
            }
            for e in cell.edges.iter().sorted_by_key(|e| e.0) {
                let mut e_node = XMLElement::new("e");
                e_node.add_attribute("a", e.0.to_string().as_str());
                e_node.add_attribute("to", e.1.to_string().as_str());
                c_node.add_child(e_node)?;
            }
            if let Some(d) = &cell.data {
                let mut data_node = XMLElement::new("data");
                data_node.add_text(d.print().replace('-', " "))?;
                c_node.add_child(data_node)?;
            }
            if let Some(name) = &cell.lambda {
                let mut lambda_node = XMLElement::new("lambda");
                lambda_node.add_text(name.clone())?;
                c_node.add_child(lambda_node)?;
            }
            root.add_child(c_node)?;
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
        g.formation(0, &[]);
        g.delta(0, &Hex::from_str_bytes("hello"));
        g.formation(1, &[]);
        g.put(0, Label::from_str("foo").unwrap(), 1);
        let xml = g.to_xml().unwrap();
        let parser = sxd_document::parser::parse(xml.as_str()).unwrap();
        let doc = parser.as_document();
        assert_eq!(
            "foo",
            evaluate_xpath(&doc, "/sodg/cell[@id=0]/e[1]/@a")
                .unwrap()
                .string(),
        );
        assert_eq!(
            "68 65 6C 6C 6F",
            evaluate_xpath(&doc, "/sodg/cell[@id=0]/data")
                .unwrap()
                .string(),
        );
    }

    #[test]
    fn prints_kinds_and_lambda() {
        let mut g: Sodg<16> = Sodg::empty(256);
        let x = Label::from_str("x").unwrap();
        g.formation(0, &[x]);
        g.lambda(0, "L_foo");
        g.dispatch(1, 0, x);
        let xml = g.to_xml().unwrap();
        let parser = sxd_document::parser::parse(xml.as_str()).unwrap();
        let doc = parser.as_document();
        assert_eq!(
            "formation",
            evaluate_xpath(&doc, "/sodg/cell[@id=0]/@kind")
                .unwrap()
                .string(),
        );
        assert_eq!(
            "L_foo",
            evaluate_xpath(&doc, "/sodg/cell[@id=0]/lambda")
                .unwrap()
                .string(),
        );
        assert_eq!(
            "x",
            evaluate_xpath(&doc, "/sodg/cell[@id=1][@kind='dispatch']/@attr")
                .unwrap()
                .string(),
        );
    }

    #[test]
    fn keeps_read_cells_in_xml() {
        let mut g: Sodg<16> = Sodg::empty(256);
        g.formation(1, &[]);
        g.formation(2, &[]);
        g.put(1, Label::Alpha(0), 2);
        g.delta(2, &Hex::from_str_bytes("hello"));
        assert!(g.data(2).is_some());
        assert_eq!(2, g.len());
        let xml = g.to_xml().unwrap();
        assert_eq!(2, xml.matches("<cell").count());
        assert!(xml.contains("<data>"));
    }
}
