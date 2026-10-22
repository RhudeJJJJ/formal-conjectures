/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4258 : Family 9 := level9.get ⟨242,by decide⟩
def sourceMap4258 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,14,15,13,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap4258 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4258_checked : acceptsGraphIso
    (source (graph core4258) (root 9) 2 2) DegreeTwoThreeSpectrum4859.graph sourceMap4258=true := by decide +kernel
theorem fusedMap4258_checked : acceptsGraphIso
    (fused (graph core4258) (root 9) 2 2) DegreeTwoThreeSpectrum4039.graph fusedMap4258=true := by decide +kernel
theorem certified4258 : Certified (graph core4258) (root 9) 2 2 :=
  of_native_maps core4258 DegreeTwoThreeSpectrum4859.graph DegreeTwoThreeSpectrum4039.graph
    sourceMap4258 fusedMap4258 sourceMap4258_checked fusedMap4258_checked
    DegreeTwoThreeFiniteComparisons.comparison4258
#print axioms sourceMap4258_checked
#print axioms fusedMap4258_checked
#print axioms certified4258
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
