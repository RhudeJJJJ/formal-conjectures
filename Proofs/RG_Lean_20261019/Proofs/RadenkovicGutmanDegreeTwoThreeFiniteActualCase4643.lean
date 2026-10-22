/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4643 : Family 10 := level10.get ⟨721,by decide⟩
def sourceMap4643 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4643 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4643_checked : acceptsGraphIso
    (source (graph core4643) (root 10) 2 2) DegreeTwoThreeSpectrum7371.graph sourceMap4643=true := by decide +kernel
theorem fusedMap4643_checked : acceptsGraphIso
    (fused (graph core4643) (root 10) 2 2) DegreeTwoThreeSpectrum5471.graph fusedMap4643=true := by decide +kernel
theorem certified4643 : Certified (graph core4643) (root 10) 2 2 :=
  of_native_maps core4643 DegreeTwoThreeSpectrum7371.graph DegreeTwoThreeSpectrum5471.graph
    sourceMap4643 fusedMap4643 sourceMap4643_checked fusedMap4643_checked
    DegreeTwoThreeFiniteComparisons.comparison4643
#print axioms sourceMap4643_checked
#print axioms fusedMap4643_checked
#print axioms certified4643
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
