/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4358 : Family 9 := level9.get ⟨497,by decide⟩
def sourceMap4358 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,9,10,11,12,13,14,15,7,8,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap4358 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4358_checked : acceptsGraphIso
    (source (graph core4358) (root 9) 2 2) DegreeTwoThreeSpectrum4874.graph sourceMap4358=true := by decide +kernel
theorem fusedMap4358_checked : acceptsGraphIso
    (fused (graph core4358) (root 9) 2 2) DegreeTwoThreeSpectrum4574.graph fusedMap4358=true := by decide +kernel
theorem certified4358 : Certified (graph core4358) (root 9) 2 2 :=
  of_native_maps core4358 DegreeTwoThreeSpectrum4874.graph DegreeTwoThreeSpectrum4574.graph
    sourceMap4358 fusedMap4358 sourceMap4358_checked fusedMap4358_checked
    DegreeTwoThreeFiniteComparisons.comparison4358
#print axioms sourceMap4358_checked
#print axioms fusedMap4358_checked
#print axioms certified4358
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
