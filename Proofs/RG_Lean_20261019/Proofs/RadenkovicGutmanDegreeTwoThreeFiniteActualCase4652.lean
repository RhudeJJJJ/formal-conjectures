/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4652 : Family 10 := level10.get ⟨749,by decide⟩
def sourceMap4652 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4652 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4652_checked : acceptsGraphIso
    (source (graph core4652) (root 10) 2 2) DegreeTwoThreeSpectrum7414.graph sourceMap4652=true := by decide +kernel
theorem fusedMap4652_checked : acceptsGraphIso
    (fused (graph core4652) (root 10) 2 2) DegreeTwoThreeSpectrum5512.graph fusedMap4652=true := by decide +kernel
theorem certified4652 : Certified (graph core4652) (root 10) 2 2 :=
  of_native_maps core4652 DegreeTwoThreeSpectrum7414.graph DegreeTwoThreeSpectrum5512.graph
    sourceMap4652 fusedMap4652 sourceMap4652_checked fusedMap4652_checked
    DegreeTwoThreeFiniteComparisons.comparison4652
#print axioms sourceMap4652_checked
#print axioms fusedMap4652_checked
#print axioms certified4652
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
