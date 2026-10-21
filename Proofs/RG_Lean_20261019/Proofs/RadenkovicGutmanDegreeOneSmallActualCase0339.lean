/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0339 : Family 6 := level6.get ⟨10,by decide⟩
def sourceMap0339 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,4,5,6,7,8,2,3] (sourceLabel 6 0 0 v)
def fusedMap0339 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![6,0,1,2,3,4,5,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap0339_checked : acceptsGraphIso
    (source (graph core0339) (root 6) 0 0) DegreeOneSmallSpectrum049.graph sourceMap0339=true := by decide +kernel
theorem fusedMap0339_checked : acceptsGraphIso
    (fused (graph core0339) (root 6) 0 0) DegreeOneSmallSpectrum055.graph fusedMap0339=true := by decide +kernel
theorem certified0339 : Certified (graph core0339) (root 6) 0 0 :=
  of_native_maps core0339 DegreeOneSmallSpectrum049.graph DegreeOneSmallSpectrum055.graph
    sourceMap0339 fusedMap0339 sourceMap0339_checked fusedMap0339_checked
    DegreeOneSmallComparisons.comparison0339
#print axioms sourceMap0339_checked
#print axioms fusedMap0339_checked
#print axioms certified0339
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
