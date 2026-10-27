/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4137 : Family 8 := level8.get ⟨138,by decide⟩
def sourceMap4137 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4137 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4137_checked : acceptsGraphIso
    (source (graph core4137) (root 8) 2 2) DegreeTwoThreeSpectrum3440.graph sourceMap4137=true := by decide +kernel
theorem fusedMap4137_checked : acceptsGraphIso
    (fused (graph core4137) (root 8) 2 2) DegreeTwoThreeSpectrum2670.graph fusedMap4137=true := by decide +kernel
theorem certified4137 : Certified (graph core4137) (root 8) 2 2 :=
  of_native_maps core4137 DegreeTwoThreeSpectrum3440.graph DegreeTwoThreeSpectrum2670.graph
    sourceMap4137 fusedMap4137 sourceMap4137_checked fusedMap4137_checked
    DegreeTwoThreeFiniteComparisons.comparison4137
#print axioms sourceMap4137_checked
#print axioms fusedMap4137_checked
#print axioms certified4137
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
