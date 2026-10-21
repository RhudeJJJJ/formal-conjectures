/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1782 : Family 10 := level10.get ⟨16,by decide⟩
def sourceMap1782 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1782 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1782_checked : acceptsGraphIso
    (source (graph core1782) (root 10) 0 0) DegreeOneSmallSpectrum875.graph sourceMap1782=true := by decide +kernel
theorem fusedMap1782_checked : acceptsGraphIso
    (fused (graph core1782) (root 10) 0 0) DegreeOneSmallSpectrum904.graph fusedMap1782=true := by decide +kernel
theorem certified1782 : Certified (graph core1782) (root 10) 0 0 :=
  of_native_maps core1782 DegreeOneSmallSpectrum875.graph DegreeOneSmallSpectrum904.graph
    sourceMap1782 fusedMap1782 sourceMap1782_checked fusedMap1782_checked
    DegreeOneSmallComparisons.comparison1782
#print axioms sourceMap1782_checked
#print axioms fusedMap1782_checked
#print axioms certified1782
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
