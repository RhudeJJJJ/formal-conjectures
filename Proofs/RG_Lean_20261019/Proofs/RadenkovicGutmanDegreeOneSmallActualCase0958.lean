/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0958 : Family 8 := level8.get ⟨76,by decide⟩
def sourceMap0958 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0958 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0958_checked : acceptsGraphIso
    (source (graph core0958) (root 8) 1 1) DegreeOneSmallSpectrum1329.graph sourceMap0958=true := by decide +kernel
theorem fusedMap0958_checked : acceptsGraphIso
    (fused (graph core0958) (root 8) 1 1) DegreeOneSmallSpectrum953.graph fusedMap0958=true := by decide +kernel
theorem certified0958 : Certified (graph core0958) (root 8) 1 1 :=
  of_native_maps core0958 DegreeOneSmallSpectrum1329.graph DegreeOneSmallSpectrum953.graph
    sourceMap0958 fusedMap0958 sourceMap0958_checked fusedMap0958_checked
    DegreeOneSmallComparisons.comparison0958
#print axioms sourceMap0958_checked
#print axioms fusedMap0958_checked
#print axioms certified0958
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
