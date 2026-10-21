/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1819 : Family 10 := level10.get ⟨63,by decide⟩
def sourceMap1819 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1819 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1819_checked : acceptsGraphIso
    (source (graph core1819) (root 10) 0 0) DegreeOneSmallSpectrum1163.graph sourceMap1819=true := by decide +kernel
theorem fusedMap1819_checked : acceptsGraphIso
    (fused (graph core1819) (root 10) 0 0) DegreeOneSmallSpectrum874.graph fusedMap1819=true := by decide +kernel
theorem certified1819 : Certified (graph core1819) (root 10) 0 0 :=
  of_native_maps core1819 DegreeOneSmallSpectrum1163.graph DegreeOneSmallSpectrum874.graph
    sourceMap1819 fusedMap1819 sourceMap1819_checked fusedMap1819_checked
    DegreeOneSmallComparisons.comparison1819
#print axioms sourceMap1819_checked
#print axioms fusedMap1819_checked
#print axioms certified1819
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
