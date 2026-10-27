/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4110 : Family 8 := level8.get ⟨60,by decide⟩
def sourceMap4110 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4110 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4110_checked : acceptsGraphIso
    (source (graph core4110) (root 8) 2 2) DegreeTwoThreeSpectrum3517.graph sourceMap4110=true := by decide +kernel
theorem fusedMap4110_checked : acceptsGraphIso
    (fused (graph core4110) (root 8) 2 2) DegreeTwoThreeSpectrum2357.graph fusedMap4110=true := by decide +kernel
theorem certified4110 : Certified (graph core4110) (root 8) 2 2 :=
  of_native_maps core4110 DegreeTwoThreeSpectrum3517.graph DegreeTwoThreeSpectrum2357.graph
    sourceMap4110 fusedMap4110 sourceMap4110_checked fusedMap4110_checked
    DegreeTwoThreeFiniteComparisons.comparison4110
#print axioms sourceMap4110_checked
#print axioms fusedMap4110_checked
#print axioms certified4110
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
