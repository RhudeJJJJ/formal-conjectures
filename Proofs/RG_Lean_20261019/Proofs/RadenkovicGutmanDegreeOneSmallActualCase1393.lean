/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1393 : Family 9 := level9.get ⟨142,by decide⟩
def sourceMap1393 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (sourceLabel 9 0 0 v)
def fusedMap1393 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1393_checked : acceptsGraphIso
    (source (graph core1393) (root 9) 0 0) DegreeOneSmallSpectrum637.graph sourceMap1393=true := by decide +kernel
theorem fusedMap1393_checked : acceptsGraphIso
    (fused (graph core1393) (root 9) 0 0) DegreeOneSmallSpectrum405.graph fusedMap1393=true := by decide +kernel
theorem certified1393 : Certified (graph core1393) (root 9) 0 0 :=
  of_native_maps core1393 DegreeOneSmallSpectrum637.graph DegreeOneSmallSpectrum405.graph
    sourceMap1393 fusedMap1393 sourceMap1393_checked fusedMap1393_checked
    DegreeOneSmallComparisons.comparison1393
#print axioms sourceMap1393_checked
#print axioms fusedMap1393_checked
#print axioms certified1393
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
