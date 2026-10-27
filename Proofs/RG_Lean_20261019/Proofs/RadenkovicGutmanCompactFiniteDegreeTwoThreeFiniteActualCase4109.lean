/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4109 : Family 8 := level8.get ⟨56,by decide⟩
def sourceMap4109 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4109 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4109_checked : acceptsGraphIso
    (source (graph core4109) (root 8) 2 2) DegreeTwoThreeSpectrum3448.graph sourceMap4109=true := by decide +kernel
theorem fusedMap4109_checked : acceptsGraphIso
    (fused (graph core4109) (root 8) 2 2) DegreeTwoThreeSpectrum2352.graph fusedMap4109=true := by decide +kernel
theorem certified4109 : Certified (graph core4109) (root 8) 2 2 :=
  of_native_maps core4109 DegreeTwoThreeSpectrum3448.graph DegreeTwoThreeSpectrum2352.graph
    sourceMap4109 fusedMap4109 sourceMap4109_checked fusedMap4109_checked
    DegreeTwoThreeFiniteComparisons.comparison4109
#print axioms sourceMap4109_checked
#print axioms fusedMap4109_checked
#print axioms certified4109
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
