import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
#eval do
  let h ← IO.FS.Handle.mk "build/extension/Proofs.LEAF1260_IMPORT_ONLY_TRACE.log" .append
  h.putStrLn "RG_LEAF1260_IMPORT_ONLY_CONTROL_READY"
  h.flush
namespace Gebendorfer.RadenkovicGutman.Leaf1260ImportFileTraceControl
theorem ready : True := True.intro
#print axioms ready
end Gebendorfer.RadenkovicGutman.Leaf1260ImportFileTraceControl
