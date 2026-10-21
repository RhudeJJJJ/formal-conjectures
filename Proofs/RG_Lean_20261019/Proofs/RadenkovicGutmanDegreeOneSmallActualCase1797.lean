/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1797 : Family 10 := level10.get ⟨34,by decide⟩
def sourceMap1797 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1797 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1797_checked : acceptsGraphIso
    (source (graph core1797) (root 10) 0 0) DegreeOneSmallSpectrum906.graph sourceMap1797=true := by decide +kernel
theorem fusedMap1797_checked : acceptsGraphIso
    (fused (graph core1797) (root 10) 0 0) DegreeOneSmallSpectrum974.graph fusedMap1797=true := by decide +kernel
theorem certified1797 : Certified (graph core1797) (root 10) 0 0 :=
  of_native_maps core1797 DegreeOneSmallSpectrum906.graph DegreeOneSmallSpectrum974.graph
    sourceMap1797 fusedMap1797 sourceMap1797_checked fusedMap1797_checked
    DegreeOneSmallComparisons.comparison1797
#print axioms sourceMap1797_checked
#print axioms fusedMap1797_checked
#print axioms certified1797
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
