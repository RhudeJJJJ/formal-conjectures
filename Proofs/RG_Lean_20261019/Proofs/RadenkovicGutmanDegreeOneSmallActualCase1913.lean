/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1913 : Family 10 := level10.get ⟨199,by decide⟩
def sourceMap1913 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1913 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1913_checked : acceptsGraphIso
    (source (graph core1913) (root 10) 0 0) DegreeOneSmallSpectrum1028.graph sourceMap1913=true := by decide +kernel
theorem fusedMap1913_checked : acceptsGraphIso
    (fused (graph core1913) (root 10) 0 0) DegreeOneSmallSpectrum1036.graph fusedMap1913=true := by decide +kernel
theorem certified1913 : Certified (graph core1913) (root 10) 0 0 :=
  of_native_maps core1913 DegreeOneSmallSpectrum1028.graph DegreeOneSmallSpectrum1036.graph
    sourceMap1913 fusedMap1913 sourceMap1913_checked fusedMap1913_checked
    DegreeOneSmallComparisons.comparison1913
#print axioms sourceMap1913_checked
#print axioms fusedMap1913_checked
#print axioms certified1913
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
