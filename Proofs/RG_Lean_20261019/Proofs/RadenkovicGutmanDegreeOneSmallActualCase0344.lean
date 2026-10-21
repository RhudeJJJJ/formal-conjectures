/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0344 : Family 6 := level6.get ⟨10,by decide⟩
def sourceMap0344 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (sourceLabel 6 1 1 v)
def fusedMap0344 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0344_checked : acceptsGraphIso
    (source (graph core0344) (root 6) 1 1) DegreeOneSmallSpectrum325.graph sourceMap0344=true := by decide +kernel
theorem fusedMap0344_checked : acceptsGraphIso
    (fused (graph core0344) (root 6) 1 1) DegreeOneSmallSpectrum202.graph fusedMap0344=true := by decide +kernel
theorem certified0344 : Certified (graph core0344) (root 6) 1 1 :=
  of_native_maps core0344 DegreeOneSmallSpectrum325.graph DegreeOneSmallSpectrum202.graph
    sourceMap0344 fusedMap0344 sourceMap0344_checked fusedMap0344_checked
    DegreeOneSmallComparisons.comparison0344
#print axioms sourceMap0344_checked
#print axioms fusedMap0344_checked
#print axioms certified0344
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
