/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4922 : Family 10 := level10.get ⟨1423,by decide⟩
def sourceMap4922 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,9,10,11,12,13,14,15,16,7,8,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap4922 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4922_checked : acceptsGraphIso
    (source (graph core4922) (root 10) 2 2) DegreeTwoThreeSpectrum7502.graph sourceMap4922=true := by decide +kernel
theorem fusedMap4922_checked : acceptsGraphIso
    (fused (graph core4922) (root 10) 2 2) DegreeTwoThreeSpectrum6877.graph fusedMap4922=true := by decide +kernel
theorem certified4922 : Certified (graph core4922) (root 10) 2 2 :=
  of_native_maps core4922 DegreeTwoThreeSpectrum7502.graph DegreeTwoThreeSpectrum6877.graph
    sourceMap4922 fusedMap4922 sourceMap4922_checked fusedMap4922_checked
    DegreeTwoThreeFiniteComparisons.comparison4922
#print axioms sourceMap4922_checked
#print axioms fusedMap4922_checked
#print axioms certified4922
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
