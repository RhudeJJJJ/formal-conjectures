/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4404 : Family 9 := level9.get ⟨604,by decide⟩
def sourceMap4404 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4404 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4404_checked : acceptsGraphIso
    (source (graph core4404) (root 9) 2 2) DegreeTwoThreeSpectrum4931.graph sourceMap4404=true := by decide +kernel
theorem fusedMap4404_checked : acceptsGraphIso
    (fused (graph core4404) (root 9) 2 2) DegreeTwoThreeSpectrum4292.graph fusedMap4404=true := by decide +kernel
theorem certified4404 : Certified (graph core4404) (root 9) 2 2 :=
  of_native_maps core4404 DegreeTwoThreeSpectrum4931.graph DegreeTwoThreeSpectrum4292.graph
    sourceMap4404 fusedMap4404 sourceMap4404_checked fusedMap4404_checked
    DegreeTwoThreeFiniteComparisons.comparison4404
#print axioms sourceMap4404_checked
#print axioms fusedMap4404_checked
#print axioms certified4404
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
