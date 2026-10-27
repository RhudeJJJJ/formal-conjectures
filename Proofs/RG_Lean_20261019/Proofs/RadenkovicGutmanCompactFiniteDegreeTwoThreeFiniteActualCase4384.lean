/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4384 : Family 9 := level9.get ⟨558,by decide⟩
def sourceMap4384 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap4384 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4384_checked : acceptsGraphIso
    (source (graph core4384) (root 9) 2 2) DegreeTwoThreeSpectrum4911.graph sourceMap4384=true := by decide +kernel
theorem fusedMap4384_checked : acceptsGraphIso
    (fused (graph core4384) (root 9) 2 2) DegreeTwoThreeSpectrum4194.graph fusedMap4384=true := by decide +kernel
theorem certified4384 : Certified (graph core4384) (root 9) 2 2 :=
  of_native_maps core4384 DegreeTwoThreeSpectrum4911.graph DegreeTwoThreeSpectrum4194.graph
    sourceMap4384 fusedMap4384 sourceMap4384_checked fusedMap4384_checked
    DegreeTwoThreeFiniteComparisons.comparison4384
#print axioms sourceMap4384_checked
#print axioms fusedMap4384_checked
#print axioms certified4384
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
