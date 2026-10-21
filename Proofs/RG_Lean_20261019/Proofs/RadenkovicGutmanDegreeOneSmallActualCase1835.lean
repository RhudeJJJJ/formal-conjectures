/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1835 : Family 10 := level10.get ⟨83,by decide⟩
def sourceMap1835 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1835 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1835_checked : acceptsGraphIso
    (source (graph core1835) (root 10) 0 0) DegreeOneSmallSpectrum1127.graph sourceMap1835=true := by decide +kernel
theorem fusedMap1835_checked : acceptsGraphIso
    (fused (graph core1835) (root 10) 0 0) DegreeOneSmallSpectrum902.graph fusedMap1835=true := by decide +kernel
theorem certified1835 : Certified (graph core1835) (root 10) 0 0 :=
  of_native_maps core1835 DegreeOneSmallSpectrum1127.graph DegreeOneSmallSpectrum902.graph
    sourceMap1835 fusedMap1835 sourceMap1835_checked fusedMap1835_checked
    DegreeOneSmallComparisons.comparison1835
#print axioms sourceMap1835_checked
#print axioms fusedMap1835_checked
#print axioms certified1835
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
