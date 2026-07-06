// Minimal rdf2hdt driver over the vendored reference hdt-cpp-1.3.3
// sources (from the pyHDT 2.3 sdist on PyPI). Converts an N-Triples
// file into an HDT container using the reference implementation's
// own generateHDT + saveToHDT path, so the output bytes are
// reference-real (PFC four-section dictionary, BitmapTriples, CRCs).
#include <HDTManager.hpp>
#include <HDTVocabulary.hpp>
#include <iostream>
#include <memory>

using namespace hdt;

int main(int argc, char **argv) {
    if (argc < 3) {
        std::cerr << "usage: mini_rdf2hdt input.nt output.hdt [baseURI]" << std::endl;
        return 2;
    }
    const char *in = argv[1];
    const char *out = argv[2];
    const char *base = argc > 3 ? argv[3] : "http://example.org/base";
    try {
        HDTSpecification spec;
        std::unique_ptr<HDT> hdtDoc(
            HDTManager::generateHDT(in, base, NTRIPLES, spec));
        hdtDoc->saveToHDT(out);
        std::cout << "wrote " << out << std::endl;
        return 0;
    } catch (std::exception &e) {
        std::cerr << "error: " << e.what() << std::endl;
        return 1;
    } catch (const char *e) {
        std::cerr << "error: " << e << std::endl;
        return 1;
    }
}
