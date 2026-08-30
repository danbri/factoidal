import L4Factoidal.Storage.BlockArtifact

namespace L4Factoidal.Storage.BlockArtifactTests

open L4Factoidal.Storage.BlockArtifact

private def bytes : ByteArray := ByteArray.mk #[1, 2, 3]
#guard (Artifact.fromPayload bytes).valid
#guard verify (digest bytes) bytes
#guard !(verify (digest bytes) (ByteArray.mk #[1, 2, 4]))

end L4Factoidal.Storage.BlockArtifactTests
