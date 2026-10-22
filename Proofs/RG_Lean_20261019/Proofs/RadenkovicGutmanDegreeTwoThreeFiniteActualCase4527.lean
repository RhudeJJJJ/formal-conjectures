/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4527 : Family 10 := level10.get ⟨380,by decide⟩
def sourceMap4527 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4527 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4527_checked : acceptsGraphIso
    (source (graph core4527) (root 10) 2 2) DegreeTwoThreeSpectrum6839.graph sourceMap4527=true := by decide +kernel
theorem fusedMap4527_checked : acceptsGraphIso
    (fused (graph core4527) (root 10) 2 2) DegreeTwoThreeSpectrum5702.graph fusedMap4527=true := by decide +kernel
theorem certified4527 : Certified (graph core4527) (root 10) 2 2 :=
  of_native_maps core4527 DegreeTwoThreeSpectrum6839.graph DegreeTwoThreeSpectrum5702.graph
    sourceMap4527 fusedMap4527 sourceMap4527_checked fusedMap4527_checked
    DegreeTwoThreeFiniteComparisons.comparison4527
#print axioms sourceMap4527_checked
#print axioms fusedMap4527_checked
#print axioms certified4527
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
