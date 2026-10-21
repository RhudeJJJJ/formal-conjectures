/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1986 : Family 10 := level10.get ⟨311,by decide⟩
def sourceMap1986 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap1986 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1986_checked : acceptsGraphIso
    (source (graph core1986) (root 10) 0 0) DegreeOneSmallSpectrum1233.graph sourceMap1986=true := by decide +kernel
theorem fusedMap1986_checked : acceptsGraphIso
    (fused (graph core1986) (root 10) 0 0) DegreeOneSmallSpectrum1380.graph fusedMap1986=true := by decide +kernel
theorem certified1986 : Certified (graph core1986) (root 10) 0 0 :=
  of_native_maps core1986 DegreeOneSmallSpectrum1233.graph DegreeOneSmallSpectrum1380.graph
    sourceMap1986 fusedMap1986 sourceMap1986_checked fusedMap1986_checked
    DegreeOneSmallComparisons.comparison1986
#print axioms sourceMap1986_checked
#print axioms fusedMap1986_checked
#print axioms certified1986
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
