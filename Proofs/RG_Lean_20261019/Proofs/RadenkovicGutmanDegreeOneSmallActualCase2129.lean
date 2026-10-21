/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2129 : Family 10 := level10.get ⟨569,by decide⟩
def sourceMap2129 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2129 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2129_checked : acceptsGraphIso
    (source (graph core2129) (root 10) 0 0) DegreeOneSmallSpectrum1760.graph sourceMap2129=true := by decide +kernel
theorem fusedMap2129_checked : acceptsGraphIso
    (fused (graph core2129) (root 10) 0 0) DegreeOneSmallSpectrum1097.graph fusedMap2129=true := by decide +kernel
theorem certified2129 : Certified (graph core2129) (root 10) 0 0 :=
  of_native_maps core2129 DegreeOneSmallSpectrum1760.graph DegreeOneSmallSpectrum1097.graph
    sourceMap2129 fusedMap2129 sourceMap2129_checked fusedMap2129_checked
    DegreeOneSmallComparisons.comparison2129
#print axioms sourceMap2129_checked
#print axioms fusedMap2129_checked
#print axioms certified2129
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
