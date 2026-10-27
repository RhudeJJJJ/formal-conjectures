/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4112 : Family 8 := level8.get ⟨67,by decide⟩
def sourceMap4112 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,14,13,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap4112 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4112_checked : acceptsGraphIso
    (source (graph core4112) (root 8) 2 2) DegreeTwoThreeSpectrum3593.graph sourceMap4112=true := by decide +kernel
theorem fusedMap4112_checked : acceptsGraphIso
    (fused (graph core4112) (root 8) 2 2) DegreeTwoThreeSpectrum2368.graph fusedMap4112=true := by decide +kernel
theorem certified4112 : Certified (graph core4112) (root 8) 2 2 :=
  of_native_maps core4112 DegreeTwoThreeSpectrum3593.graph DegreeTwoThreeSpectrum2368.graph
    sourceMap4112 fusedMap4112 sourceMap4112_checked fusedMap4112_checked
    DegreeTwoThreeFiniteComparisons.comparison4112
#print axioms sourceMap4112_checked
#print axioms fusedMap4112_checked
#print axioms certified4112
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
