/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1890 : Family 10 := level10.get ⟨159,by decide⟩
def sourceMap1890 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1890 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1890_checked : acceptsGraphIso
    (source (graph core1890) (root 10) 0 0) DegreeOneSmallSpectrum1112.graph sourceMap1890=true := by decide +kernel
theorem fusedMap1890_checked : acceptsGraphIso
    (fused (graph core1890) (root 10) 0 0) DegreeOneSmallSpectrum950.graph fusedMap1890=true := by decide +kernel
theorem certified1890 : Certified (graph core1890) (root 10) 0 0 :=
  of_native_maps core1890 DegreeOneSmallSpectrum1112.graph DegreeOneSmallSpectrum950.graph
    sourceMap1890 fusedMap1890 sourceMap1890_checked fusedMap1890_checked
    DegreeOneSmallComparisons.comparison1890
#print axioms sourceMap1890_checked
#print axioms fusedMap1890_checked
#print axioms certified1890
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
