/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0284 : Family 6 := level6.get ⟨1,by decide⟩
def sourceMap0284 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 6 2 2 v)
def fusedMap0284 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap0284_checked : acceptsGraphIso
    (source (graph core0284) (root 6) 2 2) DegreeOneSmallSpectrum1275.graph sourceMap0284=true := by decide +kernel
theorem fusedMap0284_checked : acceptsGraphIso
    (fused (graph core0284) (root 6) 2 2) DegreeOneSmallSpectrum856.graph fusedMap0284=true := by decide +kernel
theorem certified0284 : Certified (graph core0284) (root 6) 2 2 :=
  of_native_maps core0284 DegreeOneSmallSpectrum1275.graph DegreeOneSmallSpectrum856.graph
    sourceMap0284 fusedMap0284 sourceMap0284_checked fusedMap0284_checked
    DegreeOneSmallComparisons.comparison0284
#print axioms sourceMap0284_checked
#print axioms fusedMap0284_checked
#print axioms certified0284
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
