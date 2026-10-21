/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1643 : Family 9 := level9.get ⟨388,by decide⟩
def sourceMap1643 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1643 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap1643_checked : acceptsGraphIso
    (source (graph core1643) (root 9) 0 0) DegreeOneSmallSpectrum767.graph sourceMap1643=true := by decide +kernel
theorem fusedMap1643_checked : acceptsGraphIso
    (fused (graph core1643) (root 9) 0 0) DegreeOneSmallSpectrum765.graph fusedMap1643=true := by decide +kernel
theorem certified1643 : Certified (graph core1643) (root 9) 0 0 :=
  of_native_maps core1643 DegreeOneSmallSpectrum767.graph DegreeOneSmallSpectrum765.graph
    sourceMap1643 fusedMap1643 sourceMap1643_checked fusedMap1643_checked
    DegreeOneSmallComparisons.comparison1643
#print axioms sourceMap1643_checked
#print axioms fusedMap1643_checked
#print axioms certified1643
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
