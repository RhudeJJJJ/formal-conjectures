/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4183 : Family 8 := level8.get ⟨242,by decide⟩
def sourceMap4183 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,13,14,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap4183 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4183_checked : acceptsGraphIso
    (source (graph core4183) (root 8) 2 2) DegreeTwoThreeSpectrum3840.graph sourceMap4183=true := by decide +kernel
theorem fusedMap4183_checked : acceptsGraphIso
    (fused (graph core4183) (root 8) 2 2) DegreeTwoThreeSpectrum2692.graph fusedMap4183=true := by decide +kernel
theorem certified4183 : Certified (graph core4183) (root 8) 2 2 :=
  of_native_maps core4183 DegreeTwoThreeSpectrum3840.graph DegreeTwoThreeSpectrum2692.graph
    sourceMap4183 fusedMap4183 sourceMap4183_checked fusedMap4183_checked
    DegreeTwoThreeFiniteComparisons.comparison4183
#print axioms sourceMap4183_checked
#print axioms fusedMap4183_checked
#print axioms certified4183
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
