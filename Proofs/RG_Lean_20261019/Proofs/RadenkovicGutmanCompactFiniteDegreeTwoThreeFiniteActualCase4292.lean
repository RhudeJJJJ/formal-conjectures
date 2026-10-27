/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4292 : Family 9 := level9.get ⟨333,by decide⟩
def sourceMap4292 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4292 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4292_checked : acceptsGraphIso
    (source (graph core4292) (root 9) 2 2) DegreeTwoThreeSpectrum4698.graph sourceMap4292=true := by decide +kernel
theorem fusedMap4292_checked : acceptsGraphIso
    (fused (graph core4292) (root 9) 2 2) DegreeTwoThreeSpectrum4215.graph fusedMap4292=true := by decide +kernel
theorem certified4292 : Certified (graph core4292) (root 9) 2 2 :=
  of_native_maps core4292 DegreeTwoThreeSpectrum4698.graph DegreeTwoThreeSpectrum4215.graph
    sourceMap4292 fusedMap4292 sourceMap4292_checked fusedMap4292_checked
    DegreeTwoThreeFiniteComparisons.comparison4292
#print axioms sourceMap4292_checked
#print axioms fusedMap4292_checked
#print axioms certified4292
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
