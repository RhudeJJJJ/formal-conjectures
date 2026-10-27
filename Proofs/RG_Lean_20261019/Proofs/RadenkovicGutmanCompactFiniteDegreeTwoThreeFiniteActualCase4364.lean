/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4364 : Family 9 := level9.get ⟨510,by decide⟩
def sourceMap4364 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,8,9,10,11,12,13,14,15,7,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap4364 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4364_checked : acceptsGraphIso
    (source (graph core4364) (root 9) 2 2) DegreeTwoThreeSpectrum4891.graph sourceMap4364=true := by decide +kernel
theorem fusedMap4364_checked : acceptsGraphIso
    (fused (graph core4364) (root 9) 2 2) DegreeTwoThreeSpectrum4594.graph fusedMap4364=true := by decide +kernel
theorem certified4364 : Certified (graph core4364) (root 9) 2 2 :=
  of_native_maps core4364 DegreeTwoThreeSpectrum4891.graph DegreeTwoThreeSpectrum4594.graph
    sourceMap4364 fusedMap4364 sourceMap4364_checked fusedMap4364_checked
    DegreeTwoThreeFiniteComparisons.comparison4364
#print axioms sourceMap4364_checked
#print axioms fusedMap4364_checked
#print axioms certified4364
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
