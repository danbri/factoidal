import XCTest
import SwiftTreeSitter
import TreeSitterShexc

final class TreeSitterShexcTests: XCTestCase {
    func testCanLoadGrammar() throws {
        let parser = Parser()
        let language = Language(language: tree_sitter_shexc())
        XCTAssertNoThrow(try parser.setLanguage(language),
                         "Error loading Shape Expressions Compact Syntax parser grammar")
    }
}
