/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5046 : Family 10 := level10.get ⟨1755,by decide⟩
def sourceMap5046 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,12,13,14,15,16,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap5046 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5046_checked : acceptsGraphIso
    (source (graph core5046) (root 10) 2 2) DegreeTwoThreeSpectrum7647.graph sourceMap5046=true := by decide +kernel
theorem fusedMap5046_checked : acceptsGraphIso
    (fused (graph core5046) (root 10) 2 2) DegreeTwoThreeSpectrum6627.graph fusedMap5046=true := by decide +kernel
theorem certified5046 : Certified (graph core5046) (root 10) 2 2 :=
  of_native_maps core5046 DegreeTwoThreeSpectrum7647.graph DegreeTwoThreeSpectrum6627.graph
    sourceMap5046 fusedMap5046 sourceMap5046_checked fusedMap5046_checked
    DegreeTwoThreeFiniteComparisons.comparison5046
#print axioms sourceMap5046_checked
#print axioms fusedMap5046_checked
#print axioms certified5046
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
