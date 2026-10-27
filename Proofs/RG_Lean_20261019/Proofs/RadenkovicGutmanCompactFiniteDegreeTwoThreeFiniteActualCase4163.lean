/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4163 : Family 8 := level8.get ⟨200,by decide⟩
def sourceMap4163 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4163 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4163_checked : acceptsGraphIso
    (source (graph core4163) (root 8) 2 2) DegreeTwoThreeSpectrum3770.graph sourceMap4163=true := by decide +kernel
theorem fusedMap4163_checked : acceptsGraphIso
    (fused (graph core4163) (root 8) 2 2) DegreeTwoThreeSpectrum2460.graph fusedMap4163=true := by decide +kernel
theorem certified4163 : Certified (graph core4163) (root 8) 2 2 :=
  of_native_maps core4163 DegreeTwoThreeSpectrum3770.graph DegreeTwoThreeSpectrum2460.graph
    sourceMap4163 fusedMap4163 sourceMap4163_checked fusedMap4163_checked
    DegreeTwoThreeFiniteComparisons.comparison4163
#print axioms sourceMap4163_checked
#print axioms fusedMap4163_checked
#print axioms certified4163
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
