/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2432 : Family 10 := level10.get ⟨1347,by decide⟩
def sourceMap2432 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2432 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2432_checked : acceptsGraphIso
    (source (graph core2432) (root 10) 0 0) DegreeOneSmallSpectrum1967.graph sourceMap2432=true := by decide +kernel
theorem fusedMap2432_checked : acceptsGraphIso
    (fused (graph core2432) (root 10) 0 0) DegreeOneSmallSpectrum1963.graph fusedMap2432=true := by decide +kernel
theorem certified2432 : Certified (graph core2432) (root 10) 0 0 :=
  of_native_maps core2432 DegreeOneSmallSpectrum1967.graph DegreeOneSmallSpectrum1963.graph
    sourceMap2432 fusedMap2432 sourceMap2432_checked fusedMap2432_checked
    DegreeOneSmallComparisons.comparison2432
#print axioms sourceMap2432_checked
#print axioms fusedMap2432_checked
#print axioms certified2432
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
