/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1857 : Family 10 := level10.get ⟨112,by decide⟩
def sourceMap1857 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1857 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1857_checked : acceptsGraphIso
    (source (graph core1857) (root 10) 0 0) DegreeOneSmallSpectrum1154.graph sourceMap1857=true := by decide +kernel
theorem fusedMap1857_checked : acceptsGraphIso
    (fused (graph core1857) (root 10) 0 0) DegreeOneSmallSpectrum939.graph fusedMap1857=true := by decide +kernel
theorem certified1857 : Certified (graph core1857) (root 10) 0 0 :=
  of_native_maps core1857 DegreeOneSmallSpectrum1154.graph DegreeOneSmallSpectrum939.graph
    sourceMap1857 fusedMap1857 sourceMap1857_checked fusedMap1857_checked
    DegreeOneSmallComparisons.comparison1857
#print axioms sourceMap1857_checked
#print axioms fusedMap1857_checked
#print axioms certified1857
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
