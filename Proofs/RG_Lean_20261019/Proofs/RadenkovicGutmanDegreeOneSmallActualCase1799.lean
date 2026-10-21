/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1799 : Family 10 := level10.get ⟨36,by decide⟩
def sourceMap1799 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1799 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap1799_checked : acceptsGraphIso
    (source (graph core1799) (root 10) 0 0) DegreeOneSmallSpectrum886.graph sourceMap1799=true := by decide +kernel
theorem fusedMap1799_checked : acceptsGraphIso
    (fused (graph core1799) (root 10) 0 0) DegreeOneSmallSpectrum975.graph fusedMap1799=true := by decide +kernel
theorem certified1799 : Certified (graph core1799) (root 10) 0 0 :=
  of_native_maps core1799 DegreeOneSmallSpectrum886.graph DegreeOneSmallSpectrum975.graph
    sourceMap1799 fusedMap1799 sourceMap1799_checked fusedMap1799_checked
    DegreeOneSmallComparisons.comparison1799
#print axioms sourceMap1799_checked
#print axioms fusedMap1799_checked
#print axioms certified1799
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
