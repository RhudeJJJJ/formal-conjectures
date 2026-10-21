/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1832 : Family 10 := level10.get ⟨79,by decide⟩
def sourceMap1832 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1832 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1832_checked : acceptsGraphIso
    (source (graph core1832) (root 10) 0 0) DegreeOneSmallSpectrum1218.graph sourceMap1832=true := by decide +kernel
theorem fusedMap1832_checked : acceptsGraphIso
    (fused (graph core1832) (root 10) 0 0) DegreeOneSmallSpectrum906.graph fusedMap1832=true := by decide +kernel
theorem certified1832 : Certified (graph core1832) (root 10) 0 0 :=
  of_native_maps core1832 DegreeOneSmallSpectrum1218.graph DegreeOneSmallSpectrum906.graph
    sourceMap1832 fusedMap1832 sourceMap1832_checked fusedMap1832_checked
    DegreeOneSmallComparisons.comparison1832
#print axioms sourceMap1832_checked
#print axioms fusedMap1832_checked
#print axioms certified1832
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
