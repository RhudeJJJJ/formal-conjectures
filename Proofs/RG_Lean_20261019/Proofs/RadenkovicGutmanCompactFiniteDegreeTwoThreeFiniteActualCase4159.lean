/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4159 : Family 8 := level8.get ⟨190,by decide⟩
def sourceMap4159 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4159 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4159_checked : acceptsGraphIso
    (source (graph core4159) (root 8) 2 2) DegreeTwoThreeSpectrum3745.graph sourceMap4159=true := by decide +kernel
theorem fusedMap4159_checked : acceptsGraphIso
    (fused (graph core4159) (root 8) 2 2) DegreeTwoThreeSpectrum2438.graph fusedMap4159=true := by decide +kernel
theorem certified4159 : Certified (graph core4159) (root 8) 2 2 :=
  of_native_maps core4159 DegreeTwoThreeSpectrum3745.graph DegreeTwoThreeSpectrum2438.graph
    sourceMap4159 fusedMap4159 sourceMap4159_checked fusedMap4159_checked
    DegreeTwoThreeFiniteComparisons.comparison4159
#print axioms sourceMap4159_checked
#print axioms fusedMap4159_checked
#print axioms certified4159
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
