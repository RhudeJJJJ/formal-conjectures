/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1850 : Family 10 := level10.get ⟨103,by decide⟩
def sourceMap1850 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1850 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1850_checked : acceptsGraphIso
    (source (graph core1850) (root 10) 0 0) DegreeOneSmallSpectrum1172.graph sourceMap1850=true := by decide +kernel
theorem fusedMap1850_checked : acceptsGraphIso
    (fused (graph core1850) (root 10) 0 0) DegreeOneSmallSpectrum927.graph fusedMap1850=true := by decide +kernel
theorem certified1850 : Certified (graph core1850) (root 10) 0 0 :=
  of_native_maps core1850 DegreeOneSmallSpectrum1172.graph DegreeOneSmallSpectrum927.graph
    sourceMap1850 fusedMap1850 sourceMap1850_checked fusedMap1850_checked
    DegreeOneSmallComparisons.comparison1850
#print axioms sourceMap1850_checked
#print axioms fusedMap1850_checked
#print axioms certified1850
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
