/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4189 : Family 8 := level8.get ⟨265,by decide⟩
def sourceMap4189 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,7,8,9,10,11,12,13,14,1,2,3,4,5,6] (sourceLabel 8 2 2 v)
def fusedMap4189 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4189_checked : acceptsGraphIso
    (source (graph core4189) (root 8) 2 2) DegreeTwoThreeSpectrum3850.graph sourceMap4189=true := by decide +kernel
theorem fusedMap4189_checked : acceptsGraphIso
    (fused (graph core4189) (root 8) 2 2) DegreeTwoThreeSpectrum3000.graph fusedMap4189=true := by decide +kernel
theorem certified4189 : Certified (graph core4189) (root 8) 2 2 :=
  of_native_maps core4189 DegreeTwoThreeSpectrum3850.graph DegreeTwoThreeSpectrum3000.graph
    sourceMap4189 fusedMap4189 sourceMap4189_checked fusedMap4189_checked
    DegreeTwoThreeFiniteComparisons.comparison4189
#print axioms sourceMap4189_checked
#print axioms fusedMap4189_checked
#print axioms certified4189
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
