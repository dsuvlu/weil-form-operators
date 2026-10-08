"""Use release styling without writing to its shared FIGURE_DIR."""
import importlib.util
from research_runtime import EXPERIMENTS, output_dir

_spec = importlib.util.spec_from_file_location("_research_release_presentation", EXPERIMENTS / "presentation.py")
_style = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_style)
_style.FIGURE_DIR = output_dir() / "figures"

def __getattr__(name):
    return getattr(_style, name)
