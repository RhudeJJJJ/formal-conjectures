/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1878 : Family 10 := level10.get ⟨141,by decide⟩
def sourceMap1878 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1878 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1878_checked : acceptsGraphIso
    (source (graph core1878) (root 10) 0 0) DegreeOneSmallSpectrum1134.graph sourceMap1878=true := by decide +kernel
theorem fusedMap1878_checked : acceptsGraphIso
    (fused (graph core1878) (root 10) 0 0) DegreeOneSmallSpectrum954.graph fusedMap1878=true := by decide +kernel
theorem certified1878 : Certified (graph core1878) (root 10) 0 0 :=
  of_native_maps core1878 DegreeOneSmallSpectrum1134.graph DegreeOneSmallSpectrum954.graph
    sourceMap1878 fusedMap1878 sourceMap1878_checked fusedMap1878_checked
    DegreeOneSmallComparisons.comparison1878
#print axioms sourceMap1878_checked
#print axioms fusedMap1878_checked
#print axioms certified1878
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
