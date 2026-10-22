/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4276 : Family 9 := level9.get ⟨291,by decide⟩
def sourceMap4276 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4276 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4276_checked : acceptsGraphIso
    (source (graph core4276) (root 9) 2 2) DegreeTwoThreeSpectrum4896.graph sourceMap4276=true := by decide +kernel
theorem fusedMap4276_checked : acceptsGraphIso
    (fused (graph core4276) (root 9) 2 2) DegreeTwoThreeSpectrum4119.graph fusedMap4276=true := by decide +kernel
theorem certified4276 : Certified (graph core4276) (root 9) 2 2 :=
  of_native_maps core4276 DegreeTwoThreeSpectrum4896.graph DegreeTwoThreeSpectrum4119.graph
    sourceMap4276 fusedMap4276 sourceMap4276_checked fusedMap4276_checked
    DegreeTwoThreeFiniteComparisons.comparison4276
#print axioms sourceMap4276_checked
#print axioms fusedMap4276_checked
#print axioms certified4276
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
