module.exports = function(eleventyConfig) {
  eleventyConfig.addPassthroughCopy("**/*.html");

  return {
    dir: {
      input: ".",
      output: "_site",
      includes: "_includes",
      data: "_data"
    },
    markdownTemplateEngine: "njk",
    htmlTemplateEngine: "njk",
    pathPrefix: "/factoidal/"
  };
};
