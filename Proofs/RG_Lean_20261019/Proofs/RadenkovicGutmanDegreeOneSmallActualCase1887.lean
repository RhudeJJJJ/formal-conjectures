/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1887 : Family 10 := level10.get ⟨155,by decide⟩
def sourceMap1887 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1887 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1887_checked : acceptsGraphIso
    (source (graph core1887) (root 10) 0 0) DegreeOneSmallSpectrum1211.graph sourceMap1887=true := by decide +kernel
theorem fusedMap1887_checked : acceptsGraphIso
    (fused (graph core1887) (root 10) 0 0) DegreeOneSmallSpectrum970.graph fusedMap1887=true := by decide +kernel
theorem certified1887 : Certified (graph core1887) (root 10) 0 0 :=
  of_native_maps core1887 DegreeOneSmallSpectrum1211.graph DegreeOneSmallSpectrum970.graph
    sourceMap1887 fusedMap1887 sourceMap1887_checked fusedMap1887_checked
    DegreeOneSmallComparisons.comparison1887
#print axioms sourceMap1887_checked
#print axioms fusedMap1887_checked
#print axioms certified1887
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
