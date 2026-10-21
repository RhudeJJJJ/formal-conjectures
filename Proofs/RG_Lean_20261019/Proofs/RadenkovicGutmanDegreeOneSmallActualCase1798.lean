/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1798 : Family 10 := level10.get ⟨35,by decide⟩
def sourceMap1798 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1798 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1798_checked : acceptsGraphIso
    (source (graph core1798) (root 10) 0 0) DegreeOneSmallSpectrum893.graph sourceMap1798=true := by decide +kernel
theorem fusedMap1798_checked : acceptsGraphIso
    (fused (graph core1798) (root 10) 0 0) DegreeOneSmallSpectrum976.graph fusedMap1798=true := by decide +kernel
theorem certified1798 : Certified (graph core1798) (root 10) 0 0 :=
  of_native_maps core1798 DegreeOneSmallSpectrum893.graph DegreeOneSmallSpectrum976.graph
    sourceMap1798 fusedMap1798 sourceMap1798_checked fusedMap1798_checked
    DegreeOneSmallComparisons.comparison1798
#print axioms sourceMap1798_checked
#print axioms fusedMap1798_checked
#print axioms certified1798
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
