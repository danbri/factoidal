package tree_sitter_shexc_test

import (
	"testing"

	tree_sitter "github.com/tree-sitter/go-tree-sitter"
	tree_sitter_shexc "github.com/ericprud/tree-sitter-shexc/bindings/go"
)

func TestCanLoadGrammar(t *testing.T) {
	language := tree_sitter.NewLanguage(tree_sitter_shexc.Language())
	if language == nil {
		t.Errorf("Error loading Shape Expressions Compact Syntax parser grammar")
	}
}
