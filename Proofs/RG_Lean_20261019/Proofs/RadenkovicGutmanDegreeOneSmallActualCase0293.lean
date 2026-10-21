/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0293 : Family 6 := level6.get ⟨2,by decide⟩
def sourceMap0293 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 6 2 2 v)
def fusedMap0293 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap0293_checked : acceptsGraphIso
    (source (graph core0293) (root 6) 2 2) DegreeOneSmallSpectrum1439.graph sourceMap0293=true := by decide +kernel
theorem fusedMap0293_checked : acceptsGraphIso
    (fused (graph core0293) (root 6) 2 2) DegreeOneSmallSpectrum857.graph fusedMap0293=true := by decide +kernel
theorem certified0293 : Certified (graph core0293) (root 6) 2 2 :=
  of_native_maps core0293 DegreeOneSmallSpectrum1439.graph DegreeOneSmallSpectrum857.graph
    sourceMap0293 fusedMap0293 sourceMap0293_checked fusedMap0293_checked
    DegreeOneSmallComparisons.comparison0293
#print axioms sourceMap0293_checked
#print axioms fusedMap0293_checked
#print axioms certified0293
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
